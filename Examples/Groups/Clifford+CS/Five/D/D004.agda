{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D004 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0001 ; wl0002 ; wl0006 ; wl0007 ; wl0011 ; wl0015 ; wl0021 ; wl0024 ; wl0025 ; wl0031 ; wl0033 ; wl0035 ; wl0036 ; wl0044 ; wl0047 ; wl0052 ; wl0056 ; wl0057 ; wl0058 ; wl0062 ; wl0065 ; wl0067 ; wl0068 ; wl0076 ; wl0078 ; wl0085 ; wl0091 ; wl0097 ; wl0099 ; wl0108 ; wl0132 ; wl0133 ; wl0138 ; wl0139 ; wl0212 ; wl0218 ; wl0257 ; wl0296 ; wl0299 ; wl0300 ; wl0301 ; wl0302 ; wl0303 ; wl0304 ; wl0306 ; wl0307 ; wl0308 ; wl0309 ; wl0310 ; wl0311 ; wl0312 ; wl0313 ; wl0314 ; wl0317 ; wl0318 ; wl0325 ; wl0326 ; wl0327 ; wl0328 ; wl0329 ; wl0330 ; wl0331 ; wl0332 ; wl0333 ; wl0334 ; wl0335 ; wl0336 ; wl0337 ; wl0338 ; wl0339 ; wl0340 ; wl0341 ; wl0342 ; wl0343 ; wl0344 ; wl0345 ; wl0346 ; wl0347 ; wl0348 ; wl0349 ; wl0350 ; wl0351 ; wl0352 ; wl0353 ; wl0354 ; wl0355 ; wl0356 ; wl0357 ; wl0358 ; wl0359 ; wl0360 ; wp0094 ; wp0095 ; wp0096 ; wp0097 ; wp0098 ; wp0099 ; wp0100 ; wp0101 ; wp0102 ; wp0103 ; wp0104 ; wp0105 ; wp0106 ; wp0107 ; wp0108 ; wp0109 ; wp0110 ; wp0111 ; wp0112 ; wp0113 ; wp0114 ; wp0115 ; wp0116 ; wp0117 ; wp0118 ; wp0119 ; wp0120 ; wp0121 ; wp0122)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-BOXd-BOX ; lem-CS20-beta-c ; lem-CS20-beta-ci ; lem-CSd12-beta ; lem-CX23-beta ; lem-F0d ; lem-K0-pass-c ; lem-K0-pass-ci ; lem-beta-T-at2332 ; lem-c124-beta ; lem-c124-beta-at0310213442 ; lem-sym12 ; lem-sym12-at1221 ; lem-sym12-at132132 ; lem-sym23 ; lem-sym23-at1221 ; lem-sym34 ; lem-sym34-at1221 ; lem-sym34-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-BOXd-BOX-at2332 ; lem-CS12-beta-at243243 ; lem-CS20-beta-c-at1221 ; lem-CSd12-beta-at243243 ; lem-SBsymd ; lem-auto-BOX⟨0·1234⟩-∣-CS14 ; lem-auto-BOX⟨0·1234⟩-∣-CSd14 ; lem-beta-T-at122331 ; lem-c124-beta-at2332 ; lem-sym12-at2332 ; lem-sym12-at233442 ; lem-sym23-at021021 ; lem-sym23-at12213443 ; lem-sym23-at122331 ; lem-sym23-at12243143 ; lem-sym23-at13213442 ; lem-sym23-at13243142 ; lem-sym23-at2332 ; lem-sym23-at243243 ; lem-sym23-at3443 ; lem-sym34-at12213443 ; lem-sym34-at122331 ; lem-sym34-at12233441 ; lem-sym34-at13213442 ; lem-sym34-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-CS12-beta-at12243143 ; lem-SBsym-at0113203442 ; lem-T312-beta-at12233441 ; lem-auto-BOX⟨0·1234⟩-∣-BOX⟨0·1234⟩ ; lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at2332 ; lem-auto-BOX⟨0·1234⟩-∣-K0 ; lem-auto-BOX⟨0·1234⟩-∣-Kd0 ; lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩ ; lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩ ; lem-sym23-at02102331)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-nat-1-BOX⟨0·2134⟩ ; lem-nat-2-BOX⟨0·1234⟩ ; lem-nat-2-BOX⟨0·1324⟩ ; lem-nat-2-BOX⟨0·3412⟩ ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ013 ; lem-nat-2-TOFF301 ; lem-nat-3-BOX⟨0·1423⟩)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-2-BOX⟨0·2413⟩ ; lem-nat-2-CCZ124 ; lem-nat-2-CCZ134 ; lem-nat-2-TOFF201 ; lem-nat-3-BOX⟨0·1324⟩)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-0-CCZ014 ; lem-nat-0-TOFF403)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-TOFF413 ; lem-nat-1-BOX⟨0·1234⟩ ; lem-nat-3-TOFF301)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-BOX⟨0·1234⟩ ; lem-nat-0-BOX⟨1·0234⟩ ; lem-nat-1-BOX⟨1·0234⟩ ; lem-nat-1-BOX⟨2·0134⟩ ; lem-nat-1-TOFF401 ; lem-nat-2-TOFF402)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-0-BOX⟨0·1324⟩ ; lem-nat-0-BOX⟨1·2304⟩ ; lem-nat-1-BOX⟨1·0324⟩ ; lem-nat-1-CS01 ; lem-nat-1-CS02 ; lem-nat-2-CS12 ; lem-nat-2-CS13)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-1-CSd02 ; lem-nat-2-BOX⟨0·1432⟩ ; lem-nat-2-CS02 ; lem-nat-2-CSd02 ; lem-nat-2-SBOX⟨0·1·23·4⟩ ; lem-nat-2-SBOX⟨0·1·32·4⟩ ; lem-nat-2-SBOX⟨0·1·4·2⟩ ; lem-nat-2-SBOX⟨0·1·4·3⟩ ; lem-nat-2-SBOXd⟨0·1·4·2⟩ ; lem-nat-2-SBOXd⟨0·1·4·3⟩ ; lem-nat-2-TOFF403 ; lem-nat-3-CS23 ; lem-nat-3-CS24 ; lem-nat-3-SBOX⟨0·1·3·2⟩ ; lem-nat-3-SBOX⟨0·1·4·2⟩ ; lem-nat-3-SBOXd⟨0·1·3·2⟩ ; lem-nat-3-SBOXd⟨0·1·4·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-0-BOX⟨1·0324⟩ ; lem-nat-1-BOX⟨2·0314⟩ ; lem-nat-1-CSd01 ; lem-nat-3-CS04 ; lem-nat-3-CSd04 ; lem-nat-3-TOFF401)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-comm-CCZ024-CX13 ; lem-comm-CSd03-CCZ124 ; lem-nat-0-BOX⟨0·3124⟩ ; lem-nat-0-BOX⟨1·3024⟩ ; lem-nat-0-BOX⟨2·0134⟩ ; lem-nat-0-BOX⟨2·0314⟩ ; lem-nat-0-BOX⟨2·1034⟩ ; lem-nat-0-BOX⟨2·1304⟩ ; lem-nat-0-BOX⟨2·3104⟩ ; lem-nat-0-BOXd⟨0·1234⟩ ; lem-nat-0-BOXd⟨1·0234⟩ ; lem-nat-0-BOXd⟨4·0231⟩ ; lem-nat-0-BOXd⟨4·1230⟩ ; lem-nat-0-SBOXd⟨0·1·23·4⟩ ; lem-nat-0-SBOXd⟨1·0·32·4⟩ ; lem-nat-0-SBOXd⟨4·0·23·1⟩ ; lem-nat-1-BOX⟨2·3014⟩ ; lem-nat-1-BOXd⟨1·0234⟩ ; lem-nat-1-BOXd⟨2·0134⟩ ; lem-nat-1-BOXd⟨4·0132⟩ ; lem-nat-1-BOXd⟨4·0231⟩ ; lem-nat-1-SBOXd⟨1·0·32·4⟩ ; lem-nat-1-SBOXd⟨2·0·13·4⟩ ; lem-nat-1-SBOXd⟨4·0·31·2⟩ ; lem-nat-1-TOFF402 ; lem-nat-2-BOX⟨0·1423⟩ ; lem-nat-2-BOXd⟨2·0134⟩ ; lem-nat-2-BOXd⟨3·0124⟩ ; lem-nat-2-BOXd⟨4·0123⟩ ; lem-nat-2-BOXd⟨4·0132⟩ ; lem-nat-2-CS03 ; lem-nat-2-CSd03 ; lem-nat-2-SBOX⟨0·1·2·3⟩ ; lem-nat-2-SBOX⟨0·1·3·2⟩ ; lem-nat-2-SBOXd⟨0·1·23·4⟩ ; lem-nat-2-SBOXd⟨0·1·2·3⟩ ; lem-nat-2-SBOXd⟨0·1·32·4⟩ ; lem-nat-2-SBOXd⟨0·1·3·2⟩ ; lem-nat-2-SBOXd⟨1·0·23·4⟩ ; lem-nat-2-SBOXd⟨4·0·32·1⟩ ; lem-nat-3-BOXd⟨3·0124⟩ ; lem-nat-3-BOXd⟨4·0123⟩ ; lem-nat-3-CS03 ; lem-nat-3-CSd03 ; lem-nat-3-SBOXd⟨2·0·14·3⟩ ; lem-nat-3-SBOXd⟨2·0·31·4⟩ ; lem-nat-3-SBOXd⟨3·0·41·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-0-BOX⟨2·3014⟩ ; lem-nat-1-BOX⟨1·3024⟩)
-- auto BOXd(0;1234) | CS14: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-CS14 : Ws → ⟪ (Bx⁻0-1234 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Bx⁻0-1234 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CS14 c4 = run b0
  where
  b0 : Chain (Bx⁻0-1234 ∷ CS14 ∷ []) (CS14 ∷ Bx⁻0-1234 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ []) (lem-BOXd-BOX c4) ▸
       at 0 1 (Bx0-1243 ∷ []) (lem-sym34 c4) ▸
       at 0 1 (Bx0-1423 ∷ []) (lem-sym23-at3443 c4) ▸
       at 0 2 (CS14 ∷ Bx0-1423 ∷ []) (sym (lem-CS12-beta-at243243 c4)) ▸
       at 1 1 (Bx0-1243 ∷ []) (lem-sym23-at243243 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym34-at3443 c4) ▸
       at 1 1 (Bx⁻0-1234 ∷ []) (sym (lem-BOXd-BOX c4)) ▸ done


-- auto SBOXd(0;1;23;4) | CS14: 9 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS14 : Ws → ⟪ (Sb⁻0-1-23-4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS14 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb⁻0-1-23-4 ∷ CS14 ∷ []) (CS14 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ [])
  b0 = at 0 1 (Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) (refl) ▸
       at 4 2 (CS14 ∷ Bx⁻0-1234 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-CS14 c4) ▸
       at 2 1 (CS14⁻ ∷ []) (refl) ▸
       at 1 4 (CS14 ∷ Toff423 ∷ CS14⁻ ∷ Toff423 ∷ []) (sym (wl0325 (lit c4))) ▸
       at 3 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 0 1 (CS14 ∷ []) (refl) ▸
       at 0 2 (CS14 ∷ CS14 ∷ []) (wl0326 (lit c4)) ▸
       at 1 1 (Sb0-1-4-3 ∷ []) (refl) ▸ done

  b1 : Chain (CS14 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) (CS14 ∷ Sb⁻0-1-23-4 ∷ [])
  b1 = at 1 5 (Sb⁻0-1-23-4 ∷ []) (refl) ▸ done


-- SBsymd @3443: 5 steps
lem-SBsymd-at3443 : Ws → ⟪ (Sb⁻2-0-31-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-13-4 ∷ []) ⟫ʷ
lem-SBsymd-at3443 c4 = run b0
  where
  b0 : Chain (Sb⁻2-0-31-4 ∷ []) (Sb⁻2-0-13-4 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Sb⁻2-0-41-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨2·0·31·4⟩ (lit c4)) ▸
       at 1 1 (Sb⁻2-0-14-3 ∷ []) (lem-SBsymd c4) ▸
       at 0 2 (Sb⁻2-0-13-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨2·0·14·3⟩ (lit c4)) ▸
       at 1 2 [] (wl0007 (lit c4)) ▸ done


-- SBsymd @12213443: 5 steps
lem-SBsymd-at12213443 : Ws → ⟪ (Sb⁻1-0-32-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-23-4 ∷ []) ⟫ʷ
lem-SBsymd-at12213443 c4 = run b0
  where
  b0 : Chain (Sb⁻1-0-32-4 ∷ []) (Sb⁻1-0-23-4 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Sb⁻2-0-31-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·0·32·4⟩ (lit c4)) ▸
       at 1 1 (Sb⁻2-0-13-4 ∷ []) (lem-SBsymd-at3443 c4) ▸
       at 0 2 (Sb⁻1-0-23-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·13·4⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- SBsymd @13213442: 5 steps
lem-SBsymd-at13213442 : Ws → ⟪ (Sb⁻1-0-23-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-32-4 ∷ []) ⟫ʷ
lem-SBsymd-at13213442 c4 = run b0
  where
  b0 : Chain (Sb⁻1-0-23-4 ∷ []) (Sb⁻1-0-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb⁻1-0-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·23·4⟩ (lit c4)) ▸
       at 1 1 (Sb⁻1-0-23-4 ∷ []) (lem-SBsymd-at12213443 c4) ▸
       at 0 2 (Sb⁻1-0-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·23·4⟩ (lit c4)) ▸
       at 1 2 [] (wl0006 (lit c4)) ▸ done


-- SBsymd @0113203442: 5 steps
lem-SBsymd-at0113203442 : Ws → ⟪ (Sb⁻0-1-23-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-SBsymd-at0113203442 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-23-4 ∷ []) (Sb⁻0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Sb⁻1-0-23-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·23·4⟩ (lit c4)) ▸
       at 1 1 (Sb⁻1-0-32-4 ∷ []) (lem-SBsymd-at13213442 c4) ▸
       at 0 2 (Sb⁻0-1-32-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·32·4⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- auto SBOXd(0;1;23;4) | CS14 @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS14-at2332 : Ws → ⟪ (Sb⁻0-1-32-4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS14-at2332 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-32-4 ∷ CS14 ∷ []) (CS14 ∷ Sb⁻0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb⁻0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 (CS14 ∷ Sw23 ∷ []) (sym (wl0021 (lit c4))) ▸
       at 1 2 (CS14 ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS14 c4) ▸
       at 0 2 (CS14 ∷ Sw23 ∷ []) (sym (wl0021 (lit c4))) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·23·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOXd(0;1;23;4) | SBOX(0;1;4;3): 5 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩ : Ws → ⟪ (Sb⁻0-1-23-4 ∷ Sb0-1-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-4-3 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩ c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-23-4 ∷ Sb0-1-4-3 ∷ []) (Sb0-1-4-3 ∷ Sb⁻0-1-23-4 ∷ [])
  b0 = at 1 1 (CS14 ∷ []) (refl) ▸
       at 0 1 (Sb⁻0-1-32-4 ∷ []) (lem-SBsymd-at0113203442 c4) ▸
       at 0 2 (CS14 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS14-at2332 c4) ▸
       at 1 1 (Sb⁻0-1-23-4 ∷ []) (sym (lem-SBsymd-at0113203442 c4)) ▸
       at 0 1 (Sb0-1-4-3 ∷ []) (refl) ▸ done


-- auto BOXd(0;1234) | K0: 3 steps
lem-auto-BOXd⟨0·1234⟩-∣-K0 : Ws → ⟪ (Bx⁻0-1234 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ Bx⁻0-1234 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-K0 c4 = run b0
  where
  b0 : Chain (Bx⁻0-1234 ∷ K0 ∷ []) (K0 ∷ Bx⁻0-1234 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ []) (lem-BOXd-BOX c4) ▸
       at 0 2 (K0 ∷ Bx0-1234 ∷ []) (sym (lem-K0-pass-c c4)) ▸
       at 1 1 (Bx⁻0-1234 ∷ []) (sym (lem-BOXd-BOX c4)) ▸ done


-- F0d @3443: 5 steps
lem-F0d-at3443 : Ws → ⟪ (Sb⁻2-0-31-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-0-31-2 ∷ []) ⟫ʷ
lem-F0d-at3443 c4 = run b0
  where
  b0 : Chain (Sb⁻2-0-31-4 ∷ []) (Sb⁻4-0-31-2 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Sb⁻2-0-41-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨2·0·31·4⟩ (lit c4)) ▸
       at 1 1 (Sb⁻3-0-41-2 ∷ []) (lem-F0d c4) ▸
       at 0 2 (Sb⁻4-0-31-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨3·0·41·2⟩ (lit c4)) ▸
       at 1 2 [] (wl0007 (lit c4)) ▸ done


-- F0d @12213443: 5 steps
lem-F0d-at12213443 : Ws → ⟪ (Sb⁻1-0-32-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-0-32-1 ∷ []) ⟫ʷ
lem-F0d-at12213443 c4 = run b0
  where
  b0 : Chain (Sb⁻1-0-32-4 ∷ []) (Sb⁻4-0-32-1 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Sb⁻2-0-31-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·0·32·4⟩ (lit c4)) ▸
       at 1 1 (Sb⁻4-0-31-2 ∷ []) (lem-F0d-at3443 c4) ▸
       at 0 2 (Sb⁻4-0-32-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨4·0·31·2⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- F0d @13213442: 5 steps
lem-F0d-at13213442 : Ws → ⟪ (Sb⁻1-0-23-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-0-23-1 ∷ []) ⟫ʷ
lem-F0d-at13213442 c4 = run b0
  where
  b0 : Chain (Sb⁻1-0-23-4 ∷ []) (Sb⁻4-0-23-1 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb⁻1-0-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·23·4⟩ (lit c4)) ▸
       at 1 1 (Sb⁻4-0-32-1 ∷ []) (lem-F0d-at12213443 c4) ▸
       at 0 2 (Sb⁻4-0-23-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨4·0·32·1⟩ (lit c4)) ▸
       at 1 2 [] (wl0006 (lit c4)) ▸ done


-- F0d @0113203442: 5 steps
lem-F0d-at0113203442 : Ws → ⟪ (Sb⁻0-1-23-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-1-23-0 ∷ []) ⟫ʷ
lem-F0d-at0113203442 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-23-4 ∷ []) (Sb⁻4-1-23-0 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Sb⁻1-0-23-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·23·4⟩ (lit c4)) ▸
       at 1 1 (Sb⁻4-0-23-1 ∷ []) (lem-F0d-at13213442 c4) ▸
       at 0 2 (Sb⁻4-1-23-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨4·0·23·1⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- auto BOXd(0;1234) | K0 @0110: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-K0-at0110 : Ws → ⟪ (Bx⁻1-0234 ∷ K1 ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ Bx⁻1-0234 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-K0-at0110 c4 = run b0
  where
  b0 : Chain (Bx⁻1-0234 ∷ K1 ∷ []) (K1 ∷ Bx⁻1-0234 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx⁻0-1234 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·0234⟩ (lit c4)) ▸
       at 2 2 (K0 ∷ Sw01 ∷ []) (sym (wl0031 (lit c4))) ▸
       at 1 2 (K0 ∷ Bx⁻0-1234 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-K0 c4) ▸
       at 0 2 (K1 ∷ Sw01 ∷ []) (sym (wl0076 (lit c4))) ▸
       at 1 2 (Bx⁻1-0234 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨0·1234⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto BOXd(0;1234) | K0 @021021: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-K0-at021021 : Ws → ⟪ (Bx⁻2-0134 ∷ K2 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ Bx⁻2-0134 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-K0-at021021 c4 = run b0
  where
  b0 : Chain (Bx⁻2-0134 ∷ K2 ∷ []) (K2 ∷ Bx⁻2-0134 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx⁻1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·0134⟩ (lit c4)) ▸
       at 2 2 (K1 ∷ Sw12 ∷ []) (sym (wl0062 (lit c4))) ▸
       at 1 2 (K1 ∷ Bx⁻1-0234 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-K0-at0110 c4) ▸
       at 0 2 (K2 ∷ Sw12 ∷ []) (sym (wl0056 (lit c4))) ▸
       at 1 2 (Bx⁻2-0134 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨1·0234⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto BOXd(0;1234) | K0 @03102132: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-K0-at03102132 : Ws → ⟪ (Bx⁻3-0124 ∷ K3 ∷ []) ⟫ʷ ≈ ⟪ (K3 ∷ Bx⁻3-0124 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-K0-at03102132 c4 = run b0
  where
  b0 : Chain (Bx⁻3-0124 ∷ K3 ∷ []) (K3 ∷ Bx⁻3-0124 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx⁻2-0134 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨3·0124⟩ (lit c4)) ▸
       at 2 2 (K2 ∷ Sw23 ∷ []) (sym (wl0058 (lit c4))) ▸
       at 1 2 (K2 ∷ Bx⁻2-0134 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-K0-at021021 c4) ▸
       at 0 2 (K3 ∷ Sw23 ∷ []) (sym (wl0057 (lit c4))) ▸
       at 1 2 (Bx⁻3-0124 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨2·0134⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto BOXd(0;1234) | K0 @0410213243: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-K0-at0410213243 : Ws → ⟪ (Bx⁻4-0123 ∷ K4 ∷ []) ⟫ʷ ≈ ⟪ (K4 ∷ Bx⁻4-0123 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-K0-at0410213243 c4 = run b0
  where
  b0 : Chain (Bx⁻4-0123 ∷ K4 ∷ []) (K4 ∷ Bx⁻4-0123 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Bx⁻3-0124 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨4·0123⟩ (lit c4)) ▸
       at 2 2 (K3 ∷ Sw34 ∷ []) (sym (wl0068 (lit c4))) ▸
       at 1 2 (K3 ∷ Bx⁻3-0124 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-K0-at03102132 c4) ▸
       at 0 2 (K4 ∷ Sw34 ∷ []) (sym (wl0067 (lit c4))) ▸
       at 1 2 (Bx⁻4-0123 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨3·0124⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto BOXd(0;1234) | K0 @04102142: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-K0-at04102142 : Ws → ⟪ (Bx⁻4-0132 ∷ K4 ∷ []) ⟫ʷ ≈ ⟪ (K4 ∷ Bx⁻4-0132 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-K0-at04102142 c4 = run b0
  where
  b0 : Chain (Bx⁻4-0132 ∷ K4 ∷ []) (K4 ∷ Bx⁻4-0132 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx⁻4-0123 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨4·0132⟩ (lit c4)) ▸
       at 2 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸
       at 1 2 (K4 ∷ Bx⁻4-0123 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-K0-at0410213243 c4) ▸
       at 0 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸
       at 1 2 (Bx⁻4-0132 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨4·0123⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto BOXd(0;1234) | K0 @041041: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-K0-at041041 : Ws → ⟪ (Bx⁻4-0231 ∷ K4 ∷ []) ⟫ʷ ≈ ⟪ (K4 ∷ Bx⁻4-0231 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-K0-at041041 c4 = run b0
  where
  b0 : Chain (Bx⁻4-0231 ∷ K4 ∷ []) (K4 ∷ Bx⁻4-0231 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx⁻4-0132 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨4·0231⟩ (lit c4)) ▸
       at 2 2 (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑)) ▸
       at 1 2 (K4 ∷ Bx⁻4-0132 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-K0-at04102142 c4) ▸
       at 0 2 (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑)) ▸
       at 1 2 (Bx⁻4-0231 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨4·0132⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto BOXd(0;1234) | K0 @0440: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-K0-at0440 : Ws → ⟪ (Bx⁻4-1230 ∷ K4 ∷ []) ⟫ʷ ≈ ⟪ (K4 ∷ Bx⁻4-1230 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-K0-at0440 c4 = run b0
  where
  b0 : Chain (Bx⁻4-1230 ∷ K4 ∷ []) (K4 ∷ Bx⁻4-1230 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx⁻4-0231 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨4·1230⟩ (lit c4)) ▸
       at 2 2 (K4 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ ↑)) ▸
       at 1 2 (K4 ∷ Bx⁻4-0231 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-K0-at041041 c4) ▸
       at 0 2 (K4 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ ↑)) ▸
       at 1 2 (Bx⁻4-1230 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨4·0231⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto SBOXd(0;1;23;4) | K4: 13 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-K4 : Ws → ⟪ (Sb⁻0-1-23-4 ∷ K4 ∷ []) ⟫ʷ ≈ ⟪ (K4 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-K4 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb⁻0-1-23-4 ∷ K4 ∷ []) (Sb4-1-0-3 ∷ K4 ∷ Toff023 ∷ Sb⁻4-1-0-3 ∷ Toff023 ∷ Bx⁻4-1230 ∷ [])
  b0 = at 0 1 (Sb⁻4-1-23-0 ∷ []) (lem-F0d-at0113203442 c4) ▸
       at 0 1 (Sb4-1-0-3 ∷ Toff023 ∷ Sb⁻4-1-0-3 ∷ Toff023 ∷ Bx⁻4-1230 ∷ []) (refl) ▸
       at 4 2 (K4 ∷ Bx⁻4-1230 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-K0-at0440 c4) ▸
       at 3 2 (K4 ∷ Toff023 ∷ []) (sym (wp0094 c4)) ▸
       at 2 1 (CS01⁻ ∷ []) (refl) ▸
       at 2 2 (K4 ∷ CS01⁻ ∷ []) (wl0301 (lit c4)) ▸
       at 3 1 (Sb⁻4-1-0-3 ∷ []) (refl) ▸
       at 1 2 (K4 ∷ Toff023 ∷ []) (sym (wp0094 c4)) ▸ done

  b1 : Chain (Sb4-1-0-3 ∷ K4 ∷ Toff023 ∷ Sb⁻4-1-0-3 ∷ Toff023 ∷ Bx⁻4-1230 ∷ []) (K4 ∷ Sb⁻0-1-23-4 ∷ [])
  b1 = at 0 1 (CS01 ∷ []) (refl) ▸
       at 0 2 (K4 ∷ CS01 ∷ []) (wl0302 (lit c4)) ▸
       at 1 1 (Sb4-1-0-3 ∷ []) (refl) ▸
       at 1 5 (Sb⁻4-1-23-0 ∷ []) (refl) ▸
       at 1 1 (Sb⁻0-1-23-4 ∷ []) (sym (lem-F0d-at0113203442 c4)) ▸ done


-- auto BOXd(0;1234) | CS24: 9 steps
lem-auto-BOXd⟨0·1234⟩-∣-CS24 : Ws → ⟪ (Bx⁻0-1234 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ Bx⁻0-1234 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CS24 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx⁻0-1234 ∷ CS24 ∷ []) (CS24 ∷ Bx0-1234 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ []) (lem-BOXd-BOX c4) ▸
       at 0 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 0 1 (Bx0-2143 ∷ []) (lem-sym34-at1221 c4) ▸
       at 0 1 (Bx0-2413 ∷ []) (lem-sym23-at12213443 c4) ▸
       at 0 2 (CS24 ∷ Bx0-2413 ∷ []) (sym (lem-CS12-beta-at12243143 c4)) ▸
       at 1 1 (Bx0-2143 ∷ []) (lem-sym23-at12243143 c4) ▸
       at 1 1 (Bx0-2134 ∷ []) (lem-sym34-at12213443 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸ done

  b1 : Chain (CS24 ∷ Bx0-1234 ∷ []) (CS24 ∷ Bx⁻0-1234 ∷ [])
  b1 = at 1 1 (Bx⁻0-1234 ∷ []) (sym (lem-BOXd-BOX c4)) ▸ done


-- auto SBOXd(0;1;23;4) | CS24: 9 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS24 : Ws → ⟪ (Sb⁻0-1-23-4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS24 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb⁻0-1-23-4 ∷ CS24 ∷ []) (CS24 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ [])
  b0 = at 0 1 (Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) (refl) ▸
       at 4 2 (CS24 ∷ Bx⁻0-1234 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-CS24 c4) ▸
       at 2 1 (CS14⁻ ∷ []) (refl) ▸
       at 1 4 (CS24 ∷ Toff423 ∷ CS14⁻ ∷ Toff423 ∷ []) (sym (wl0327 (lit c4))) ▸
       at 3 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 0 1 (CS14 ∷ []) (refl) ▸
       at 0 2 (CS24 ∷ CS14 ∷ []) (wl0328 (lit c4)) ▸
       at 1 1 (Sb0-1-4-3 ∷ []) (refl) ▸ done

  b1 : Chain (CS24 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) (CS24 ∷ Sb⁻0-1-23-4 ∷ [])
  b1 = at 1 5 (Sb⁻0-1-23-4 ∷ []) (refl) ▸ done


-- auto BOXd(0;1234) | Kd0: 3 steps
lem-auto-BOXd⟨0·1234⟩-∣-Kd0 : Ws → ⟪ (Bx⁻0-1234 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ Bx⁻0-1234 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-Kd0 c4 = run b0
  where
  b0 : Chain (Bx⁻0-1234 ∷ K0⁻ ∷ []) (K0⁻ ∷ Bx⁻0-1234 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ []) (lem-BOXd-BOX c4) ▸
       at 0 2 (K0⁻ ∷ Bx0-1234 ∷ []) (sym (lem-K0-pass-ci c4)) ▸
       at 1 1 (Bx⁻0-1234 ∷ []) (sym (lem-BOXd-BOX c4)) ▸ done


-- auto BOXd(0;1234) | Kd0 @0110: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-Kd0-at0110 : Ws → ⟪ (Bx⁻1-0234 ∷ K1⁻ ∷ []) ⟫ʷ ≈ ⟪ (K1⁻ ∷ Bx⁻1-0234 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-Kd0-at0110 c4 = run b0
  where
  b0 : Chain (Bx⁻1-0234 ∷ K1⁻ ∷ []) (K1⁻ ∷ Bx⁻1-0234 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx⁻0-1234 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·0234⟩ (lit c4)) ▸
       at 2 2 (K0⁻ ∷ Sw01 ∷ []) (sym (wl0257 (lit c4))) ▸
       at 1 2 (K0⁻ ∷ Bx⁻0-1234 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-Kd0 c4) ▸
       at 0 2 (K1⁻ ∷ Sw01 ∷ []) (sym (wl0306 (lit c4))) ▸
       at 1 2 (Bx⁻1-0234 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨0·1234⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto BOXd(0;1234) | Kd0 @021021: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-Kd0-at021021 : Ws → ⟪ (Bx⁻2-0134 ∷ K2⁻ ∷ []) ⟫ʷ ≈ ⟪ (K2⁻ ∷ Bx⁻2-0134 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-Kd0-at021021 c4 = run b0
  where
  b0 : Chain (Bx⁻2-0134 ∷ K2⁻ ∷ []) (K2⁻ ∷ Bx⁻2-0134 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx⁻1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·0134⟩ (lit c4)) ▸
       at 2 2 (K1⁻ ∷ Sw12 ∷ []) (sym (wl0307 (lit c4))) ▸
       at 1 2 (K1⁻ ∷ Bx⁻1-0234 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-Kd0-at0110 c4) ▸
       at 0 2 (K2⁻ ∷ Sw12 ∷ []) (sym (wl0308 (lit c4))) ▸
       at 1 2 (Bx⁻2-0134 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨1·0234⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto BOXd(0;1234) | Kd0 @03102132: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-Kd0-at03102132 : Ws → ⟪ (Bx⁻3-0124 ∷ K3⁻ ∷ []) ⟫ʷ ≈ ⟪ (K3⁻ ∷ Bx⁻3-0124 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-Kd0-at03102132 c4 = run b0
  where
  b0 : Chain (Bx⁻3-0124 ∷ K3⁻ ∷ []) (K3⁻ ∷ Bx⁻3-0124 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx⁻2-0134 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨3·0124⟩ (lit c4)) ▸
       at 2 2 (K2⁻ ∷ Sw23 ∷ []) (sym (wl0309 (lit c4))) ▸
       at 1 2 (K2⁻ ∷ Bx⁻2-0134 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-Kd0-at021021 c4) ▸
       at 0 2 (K3⁻ ∷ Sw23 ∷ []) (sym (wl0310 (lit c4))) ▸
       at 1 2 (Bx⁻3-0124 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨2·0134⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto BOXd(0;1234) | Kd0 @0410213243: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-Kd0-at0410213243 : Ws → ⟪ (Bx⁻4-0123 ∷ K4⁻ ∷ []) ⟫ʷ ≈ ⟪ (K4⁻ ∷ Bx⁻4-0123 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-Kd0-at0410213243 c4 = run b0
  where
  b0 : Chain (Bx⁻4-0123 ∷ K4⁻ ∷ []) (K4⁻ ∷ Bx⁻4-0123 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Bx⁻3-0124 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨4·0123⟩ (lit c4)) ▸
       at 2 2 (K3⁻ ∷ Sw34 ∷ []) (sym (wl0311 (lit c4))) ▸
       at 1 2 (K3⁻ ∷ Bx⁻3-0124 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-Kd0-at03102132 c4) ▸
       at 0 2 (K4⁻ ∷ Sw34 ∷ []) (sym (wl0312 (lit c4))) ▸
       at 1 2 (Bx⁻4-0123 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨3·0124⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto BOXd(0;1234) | Kd0 @04102142: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-Kd0-at04102142 : Ws → ⟪ (Bx⁻4-0132 ∷ K4⁻ ∷ []) ⟫ʷ ≈ ⟪ (K4⁻ ∷ Bx⁻4-0132 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-Kd0-at04102142 c4 = run b0
  where
  b0 : Chain (Bx⁻4-0132 ∷ K4⁻ ∷ []) (K4⁻ ∷ Bx⁻4-0132 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx⁻4-0123 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨4·0132⟩ (lit c4)) ▸
       at 2 2 (K4⁻ ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K • iI)) ▸
       at 1 2 (K4⁻ ∷ Bx⁻4-0123 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-Kd0-at0410213243 c4) ▸
       at 0 2 (K4⁻ ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K • iI)) ▸
       at 1 2 (Bx⁻4-0132 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨4·0123⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto BOXd(0;1234) | Kd0 @041041: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-Kd0-at041041 : Ws → ⟪ (Bx⁻4-0231 ∷ K4⁻ ∷ []) ⟫ʷ ≈ ⟪ (K4⁻ ∷ Bx⁻4-0231 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-Kd0-at041041 c4 = run b0
  where
  b0 : Chain (Bx⁻4-0231 ∷ K4⁻ ∷ []) (K4⁻ ∷ Bx⁻4-0231 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx⁻4-0132 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨4·0231⟩ (lit c4)) ▸
       at 2 2 (K4⁻ ∷ Sw12 ∷ []) (c₃ (Swap ↑) ((K • iI) ↑)) ▸
       at 1 2 (K4⁻ ∷ Bx⁻4-0132 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-Kd0-at04102142 c4) ▸
       at 0 2 (K4⁻ ∷ Sw12 ∷ []) (c₃ (Swap ↑) ((K • iI) ↑)) ▸
       at 1 2 (Bx⁻4-0231 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨4·0132⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto BOXd(0;1234) | Kd0 @0440: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-Kd0-at0440 : Ws → ⟪ (Bx⁻4-1230 ∷ K4⁻ ∷ []) ⟫ʷ ≈ ⟪ (K4⁻ ∷ Bx⁻4-1230 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-Kd0-at0440 c4 = run b0
  where
  b0 : Chain (Bx⁻4-1230 ∷ K4⁻ ∷ []) (K4⁻ ∷ Bx⁻4-1230 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx⁻4-0231 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨4·1230⟩ (lit c4)) ▸
       at 2 2 (K4⁻ ∷ Sw01 ∷ []) (c₂ (Swap) ((K • iI) ↑ ↑)) ▸
       at 1 2 (K4⁻ ∷ Bx⁻4-0231 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-Kd0-at041041 c4) ▸
       at 0 2 (K4⁻ ∷ Sw01 ∷ []) (c₂ (Swap) ((K • iI) ↑ ↑)) ▸
       at 1 2 (Bx⁻4-1230 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨4·0231⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto SBOXd(0;1;23;4) | Kd4: 13 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-Kd4 : Ws → ⟪ (Sb⁻0-1-23-4 ∷ K4⁻ ∷ []) ⟫ʷ ≈ ⟪ (K4⁻ ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-Kd4 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb⁻0-1-23-4 ∷ K4⁻ ∷ []) (Sb4-1-0-3 ∷ K4⁻ ∷ Toff023 ∷ Sb⁻4-1-0-3 ∷ Toff023 ∷ Bx⁻4-1230 ∷ [])
  b0 = at 0 1 (Sb⁻4-1-23-0 ∷ []) (lem-F0d-at0113203442 c4) ▸
       at 0 1 (Sb4-1-0-3 ∷ Toff023 ∷ Sb⁻4-1-0-3 ∷ Toff023 ∷ Bx⁻4-1230 ∷ []) (refl) ▸
       at 4 2 (K4⁻ ∷ Bx⁻4-1230 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-Kd0-at0440 c4) ▸
       at 3 2 (K4⁻ ∷ Toff023 ∷ []) (sym (wp0095 c4)) ▸
       at 2 1 (CS01⁻ ∷ []) (refl) ▸
       at 2 2 (K4⁻ ∷ CS01⁻ ∷ []) (wl0313 (lit c4)) ▸
       at 3 1 (Sb⁻4-1-0-3 ∷ []) (refl) ▸
       at 1 2 (K4⁻ ∷ Toff023 ∷ []) (sym (wp0095 c4)) ▸ done

  b1 : Chain (Sb4-1-0-3 ∷ K4⁻ ∷ Toff023 ∷ Sb⁻4-1-0-3 ∷ Toff023 ∷ Bx⁻4-1230 ∷ []) (K4⁻ ∷ Sb⁻0-1-23-4 ∷ [])
  b1 = at 0 1 (CS01 ∷ []) (refl) ▸
       at 0 2 (K4⁻ ∷ CS01 ∷ []) (wl0314 (lit c4)) ▸
       at 1 1 (Sb4-1-0-3 ∷ []) (refl) ▸
       at 1 5 (Sb⁻4-1-23-0 ∷ []) (refl) ▸
       at 1 1 (Sb⁻0-1-23-4 ∷ []) (sym (lem-F0d-at0113203442 c4)) ▸ done


-- auto BOXd(0;1234) | CSd14: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-CSd14 : Ws → ⟪ (Bx⁻0-1234 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ Bx⁻0-1234 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CSd14 c4 = run b0
  where
  b0 : Chain (Bx⁻0-1234 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Bx⁻0-1234 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ []) (lem-BOXd-BOX c4) ▸
       at 0 1 (Bx0-1243 ∷ []) (lem-sym34 c4) ▸
       at 0 1 (Bx0-1423 ∷ []) (lem-sym23-at3443 c4) ▸
       at 0 2 (CS14⁻ ∷ Bx0-1423 ∷ []) (sym (lem-CSd12-beta-at243243 c4)) ▸
       at 1 1 (Bx0-1243 ∷ []) (lem-sym23-at243243 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym34-at3443 c4) ▸
       at 1 1 (Bx⁻0-1234 ∷ []) (sym (lem-BOXd-BOX c4)) ▸ done


-- auto SBOXd(0;1;23;4) | CSd14: 9 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CSd14 : Ws → ⟪ (Sb⁻0-1-23-4 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CSd14 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb⁻0-1-23-4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ [])
  b0 = at 0 1 (Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) (refl) ▸
       at 4 2 (CS14⁻ ∷ Bx⁻0-1234 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-CSd14 c4) ▸
       at 2 1 (CS14⁻ ∷ []) (refl) ▸
       at 1 4 (CS14⁻ ∷ Toff423 ∷ CS14⁻ ∷ Toff423 ∷ []) (sym (wl0329 (lit c4))) ▸
       at 3 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 0 1 (CS14 ∷ []) (refl) ▸
       at 0 2 (CS14⁻ ∷ CS14 ∷ []) (wl0299 (lit c4)) ▸
       at 1 1 (Sb0-1-4-3 ∷ []) (refl) ▸ done

  b1 : Chain (CS14⁻ ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) (CS14⁻ ∷ Sb⁻0-1-23-4 ∷ [])
  b1 = at 1 5 (Sb⁻0-1-23-4 ∷ []) (refl) ▸ done


-- auto SBOXd(0;1;23;4) | CSd14 @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CSd14-at2332 : Ws → ⟪ (Sb⁻0-1-32-4 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CSd14-at2332 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-32-4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Sb⁻0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb⁻0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 (CS14⁻ ∷ Sw23 ∷ []) (sym (wl0033 (lit c4))) ▸
       at 1 2 (CS14⁻ ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CSd14 c4) ▸
       at 0 2 (CS14⁻ ∷ Sw23 ∷ []) (sym (wl0033 (lit c4))) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·23·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOXd(0;1;23;4) | SBOXd(0;1;4;3): 5 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩ : Ws → ⟪ (Sb⁻0-1-23-4 ∷ Sb⁻0-1-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-4-3 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩ c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-23-4 ∷ Sb⁻0-1-4-3 ∷ []) (Sb⁻0-1-4-3 ∷ Sb⁻0-1-23-4 ∷ [])
  b0 = at 1 1 (CS14⁻ ∷ []) (refl) ▸
       at 0 1 (Sb⁻0-1-32-4 ∷ []) (lem-SBsymd-at0113203442 c4) ▸
       at 0 2 (CS14⁻ ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CSd14-at2332 c4) ▸
       at 1 1 (Sb⁻0-1-23-4 ∷ []) (sym (lem-SBsymd-at0113203442 c4)) ▸
       at 0 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸ done


-- auto SBOXd(0;1;23;4) | K0: 11 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-K0 : Ws → ⟪ (Sb⁻0-1-23-4 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-K0 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb⁻0-1-23-4 ∷ K0 ∷ []) (CS14 ∷ K0 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ [])
  b0 = at 0 1 (Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) (refl) ▸
       at 4 2 (K0 ∷ Bx⁻0-1234 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-K0 c4) ▸
       at 3 2 (K0 ∷ Toff423 ∷ []) (sym (wl0330 (lit c4))) ▸
       at 2 1 (CS14⁻ ∷ []) (refl) ▸
       at 2 2 (K0 ∷ CS14⁻ ∷ []) (wp0096 c4) ▸
       at 3 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 1 2 (K0 ∷ Toff423 ∷ []) (sym (wl0330 (lit c4))) ▸
       at 0 1 (CS14 ∷ []) (refl) ▸ done

  b1 : Chain (CS14 ∷ K0 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) (K0 ∷ Sb⁻0-1-23-4 ∷ [])
  b1 = at 0 2 (K0 ∷ CS14 ∷ []) (wp0097 c4) ▸
       at 1 1 (Sb0-1-4-3 ∷ []) (refl) ▸
       at 1 5 (Sb⁻0-1-23-4 ∷ []) (refl) ▸ done


-- auto BOXd(0;1234) | CS20: 5 steps
lem-auto-BOXd⟨0·1234⟩-∣-CS20 : Ws → ⟪ (Bx⁻0-1234 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ Bx⁻0-1234 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CS20 c4 = run b0
  where
  b0 : Chain (Bx⁻0-1234 ∷ CS02 ∷ []) (CS02 ∷ Bx⁻0-1234 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ []) (lem-BOXd-BOX c4) ▸
       at 1 1 (CS02 ∷ []) (wl0331 (lit c4)) ▸
       at 0 2 (CS02 ∷ Bx0-1234 ∷ []) (sym (lem-CS20-beta-c c4)) ▸
       at 0 1 (CS02 ∷ []) (wl0331 (lit c4)) ▸
       at 1 1 (Bx⁻0-1234 ∷ []) (sym (lem-BOXd-BOX c4)) ▸ done


-- auto SBOXd(0;1;23;4) | CS20: 11 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS20 : Ws → ⟪ (Sb⁻0-1-23-4 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS20 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb⁻0-1-23-4 ∷ CS02 ∷ []) (CS14 ∷ CS02 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ [])
  b0 = at 0 1 (Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) (refl) ▸
       at 4 2 (CS02 ∷ Bx⁻0-1234 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-CS20 c4) ▸
       at 3 2 (CS02 ∷ Toff423 ∷ []) (sym (wp0098 c4)) ▸
       at 2 1 (CS14⁻ ∷ []) (refl) ▸
       at 2 2 (CS02 ∷ CS14⁻ ∷ []) (sym (wp0099 c4)) ▸
       at 3 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 1 2 (CS02 ∷ Toff423 ∷ []) (sym (wp0098 c4)) ▸
       at 0 1 (CS14 ∷ []) (refl) ▸ done

  b1 : Chain (CS14 ∷ CS02 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) (CS02 ∷ Sb⁻0-1-23-4 ∷ [])
  b1 = at 0 2 (CS02 ∷ CS14 ∷ []) (sym (wp0100 c4)) ▸
       at 1 1 (Sb0-1-4-3 ∷ []) (refl) ▸
       at 1 5 (Sb⁻0-1-23-4 ∷ []) (refl) ▸ done


-- auto BOXd(0;1234) | CS10: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-CS10 : Ws → ⟪ (Bx⁻0-1234 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ Bx⁻0-1234 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CS10 c4 = run b0
  where
  b0 : Chain (Bx⁻0-1234 ∷ CS01 ∷ []) (CS01 ∷ Bx⁻0-1234 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ []) (lem-BOXd-BOX c4) ▸
       at 1 1 (CS01 ∷ []) (wl0332 (lit c4)) ▸
       at 0 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 0 2 (CS01 ∷ Bx0-2134 ∷ []) (sym (lem-CS20-beta-c-at1221 c4)) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸
       at 0 1 (CS01 ∷ []) (wl0332 (lit c4)) ▸
       at 1 1 (Bx⁻0-1234 ∷ []) (sym (lem-BOXd-BOX c4)) ▸ done


-- auto TOFF012 | CS34: 1 steps
lem-auto-TOFF012-∣-CS34 : Ws → ⟪ (Toff012 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ Toff012 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-CS34 c4 = run b0
  where
  b0 : Chain (Toff012 ∷ CS34 ∷ []) (CS34 ∷ Toff012 ∷ [])
  b0 = at 0 2 (CS34 ∷ Toff012 ∷ []) (c₃ (Toff) (CS)) ▸ done


-- auto TOFF012 | CS34 @0110: 7 steps
lem-auto-TOFF012-∣-CS34-at0110 : Ws → ⟪ (Toff102 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ Toff102 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-CS34-at0110 c4 = run b0
  where
  b0 : Chain (Toff102 ∷ CS34 ∷ []) (CS34 ∷ Toff102 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Toff012 ∷ Sw01 ∷ []) (wl0097 (lit c4)) ▸
       at 2 2 (CS34 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑)) ▸
       at 1 2 (CS34 ∷ Toff012 ∷ []) (lem-auto-TOFF012-∣-CS34 c4) ▸
       at 0 2 (CS34 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑)) ▸
       at 1 2 (Toff102 ∷ Sw01 ∷ []) (wl0099 (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto TOFF012 | CS34 @021021: 7 steps
lem-auto-TOFF012-∣-CS34-at021021 : Ws → ⟪ (Toff201 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ Toff201 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-CS34-at021021 c4 = run b0
  where
  b0 : Chain (Toff201 ∷ CS34 ∷ []) (CS34 ∷ Toff201 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Toff102 ∷ Sw12 ∷ []) (wl0044 (lit c4)) ▸
       at 2 2 (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸
       at 1 2 (CS34 ∷ Toff102 ∷ []) (lem-auto-TOFF012-∣-CS34-at0110 c4) ▸
       at 0 2 (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸
       at 1 2 (Toff201 ∷ Sw12 ∷ []) (wl0047 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto TOFF012 | CS34 @03102132: 7 steps
lem-auto-TOFF012-∣-CS34-at03102132 : Ws → ⟪ (Toff301 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ Toff301 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-CS34-at03102132 c4 = run b0
  where
  b0 : Chain (Toff301 ∷ CS24 ∷ []) (CS24 ∷ Toff301 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Toff201 ∷ Sw23 ∷ []) (lem-nat-2-TOFF301 (lit c4)) ▸
       at 2 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0011 (lit c4))) ▸
       at 1 2 (CS34 ∷ Toff201 ∷ []) (lem-auto-TOFF012-∣-CS34-at021021 c4) ▸
       at 0 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0015 (lit c4))) ▸
       at 1 2 (Toff301 ∷ Sw23 ∷ []) (lem-nat-2-TOFF201 (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto TOFF012 | CS34 @0410213243: 7 steps
lem-auto-TOFF012-∣-CS34-at0410213243 : Ws → ⟪ (Toff401 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ Toff401 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-CS34-at0410213243 c4 = run b0
  where
  b0 : Chain (Toff401 ∷ CS23 ∷ []) (CS23 ∷ Toff401 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Toff301 ∷ Sw34 ∷ []) (lem-nat-3-TOFF401 (lit c4)) ▸
       at 2 2 (CS24 ∷ Sw34 ∷ []) (lem-nat-3-CS23 (lit c4)) ▸
       at 1 2 (CS24 ∷ Toff301 ∷ []) (lem-auto-TOFF012-∣-CS34-at03102132 c4) ▸
       at 0 2 (CS23 ∷ Sw34 ∷ []) (lem-nat-3-CS24 (lit c4)) ▸
       at 1 2 (Toff401 ∷ Sw34 ∷ []) (lem-nat-3-TOFF301 (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto TOFF012 | CS34 @04103143: 7 steps
lem-auto-TOFF012-∣-CS34-at04103143 : Ws → ⟪ (Toff402 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Toff402 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-CS34-at04103143 c4 = run b0
  where
  b0 : Chain (Toff402 ∷ CS13 ∷ []) (CS13 ∷ Toff402 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Toff401 ∷ Sw12 ∷ []) (lem-nat-1-TOFF402 (lit c4)) ▸
       at 2 2 (CS23 ∷ Sw12 ∷ []) (sym (wl0025 (lit c4))) ▸
       at 1 2 (CS23 ∷ Toff401 ∷ []) (lem-auto-TOFF012-∣-CS34-at0410213243 c4) ▸
       at 0 2 (CS13 ∷ Sw12 ∷ []) (sym (wl0024 (lit c4))) ▸
       at 1 2 (Toff402 ∷ Sw12 ∷ []) (lem-nat-1-TOFF401 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto TOFF012 | CS34 @0410233142: 7 steps
lem-auto-TOFF012-∣-CS34-at0410233142 : Ws → ⟪ (Toff403 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ Toff403 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-CS34-at0410233142 c4 = run b0
  where
  b0 : Chain (Toff403 ∷ CS12 ∷ []) (CS12 ∷ Toff403 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Toff402 ∷ Sw23 ∷ []) (lem-nat-2-TOFF403 (lit c4)) ▸
       at 2 2 (CS13 ∷ Sw23 ∷ []) (lem-nat-2-CS12 (lit c4)) ▸
       at 1 2 (CS13 ∷ Toff402 ∷ []) (lem-auto-TOFF012-∣-CS34-at04103143 c4) ▸
       at 0 2 (CS12 ∷ Sw23 ∷ []) (lem-nat-2-CS13 (lit c4)) ▸
       at 1 2 (Toff403 ∷ Sw23 ∷ []) (lem-nat-2-TOFF402 (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto TOFF012 | CS34 @04233042: 7 steps
lem-auto-TOFF012-∣-CS34-at04233042 : Ws → ⟪ (Toff413 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ Toff413 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-CS34-at04233042 c4 = run b0
  where
  b0 : Chain (Toff413 ∷ CS02 ∷ []) (CS02 ∷ Toff413 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Toff403 ∷ Sw01 ∷ []) (lem-nat-0-TOFF413 (lit c4)) ▸
       at 2 2 (CS12 ∷ Sw01 ∷ []) (sym (wl0138 (lit c4))) ▸
       at 1 2 (CS12 ∷ Toff403 ∷ []) (lem-auto-TOFF012-∣-CS34-at0410233142 c4) ▸
       at 0 2 (CS02 ∷ Sw01 ∷ []) (sym (wl0035 (lit c4))) ▸
       at 1 2 (Toff413 ∷ Sw01 ∷ []) (lem-nat-0-TOFF403 (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto TOFF012 | CS34 @0412233041: 7 steps
lem-auto-TOFF012-∣-CS34-at0412233041 : Ws → ⟪ (Toff423 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ Toff423 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-CS34-at0412233041 c4 = run b0
  where
  b0 : Chain (Toff423 ∷ CS01 ∷ []) (CS01 ∷ Toff423 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Toff413 ∷ Sw12 ∷ []) (wl0091 (lit c4)) ▸
       at 2 2 (CS02 ∷ Sw12 ∷ []) (lem-nat-1-CS01 (lit c4)) ▸
       at 1 2 (CS02 ∷ Toff413 ∷ []) (lem-auto-TOFF012-∣-CS34-at04233042 c4) ▸
       at 0 2 (CS01 ∷ Sw12 ∷ []) (lem-nat-1-CS02 (lit c4)) ▸
       at 1 2 (Toff423 ∷ Sw12 ∷ []) (wl0085 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto TOFF012 | CS34 @0412233140: 7 steps
lem-auto-TOFF012-∣-CS34-at0412233140 : Ws → ⟪ (Toff423 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ Toff423 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-CS34-at0412233140 c4 = run b0
  where
  b0 : Chain (Toff423 ∷ CS01 ∷ []) (CS01 ∷ Toff423 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Toff423 ∷ Sw01 ∷ []) (c₂ (Swap) (Toffᵗ)) ▸
       at 2 2 (CS01 ∷ Sw01 ∷ []) (sym (wl0132 (lit c4))) ▸
       at 1 2 (CS01 ∷ Toff423 ∷ []) (lem-auto-TOFF012-∣-CS34-at0412233041 c4) ▸
       at 0 2 (CS01 ∷ Sw01 ∷ []) (sym (wl0132 (lit c4))) ▸
       at 1 2 (Toff423 ∷ Sw01 ∷ []) (c₂ (Swap) (Toffᵗ)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto SBOXd(0;1;23;4) | CS10: 11 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS10 : Ws → ⟪ (Sb⁻0-1-23-4 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS10 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb⁻0-1-23-4 ∷ CS01 ∷ []) (CS14 ∷ CS01 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ [])
  b0 = at 0 1 (Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) (refl) ▸
       at 4 2 (CS01 ∷ Bx⁻0-1234 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-CS10 c4) ▸
       at 3 2 (CS01 ∷ Toff423 ∷ []) (lem-auto-TOFF012-∣-CS34-at0412233140 c4) ▸
       at 2 1 (CS14⁻ ∷ []) (refl) ▸
       at 2 2 (CS01 ∷ CS14⁻ ∷ []) (sym (wp0101 c4)) ▸
       at 3 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 1 2 (CS01 ∷ Toff423 ∷ []) (lem-auto-TOFF012-∣-CS34-at0412233140 c4) ▸
       at 0 1 (CS14 ∷ []) (refl) ▸ done

  b1 : Chain (CS14 ∷ CS01 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) (CS01 ∷ Sb⁻0-1-23-4 ∷ [])
  b1 = at 0 2 (CS01 ∷ CS14 ∷ []) (sym (wp0102 c4)) ▸
       at 1 1 (Sb0-1-4-3 ∷ []) (refl) ▸
       at 1 5 (Sb⁻0-1-23-4 ∷ []) (refl) ▸ done


-- auto SBOXd(0;1;23;4) | CS20 @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS20-at2332 : Ws → ⟪ (Sb⁻0-1-32-4 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS20-at2332 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-32-4 ∷ CS03 ∷ []) (CS03 ∷ Sb⁻0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb⁻0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 (CS02 ∷ Sw23 ∷ []) (lem-nat-2-CS03 (lit c4)) ▸
       at 1 2 (CS02 ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS20 c4) ▸
       at 0 2 (CS03 ∷ Sw23 ∷ []) (lem-nat-2-CS02 (lit c4)) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·23·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOXd(0;1;23;4) | CS10 @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS10-at2332 : Ws → ⟪ (Sb⁻0-1-32-4 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS10-at2332 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-32-4 ∷ CS01 ∷ []) (CS01 ∷ Sb⁻0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb⁻0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 (CS01 ∷ Sw23 ∷ []) (sym (c₂ (CS) (Swap))) ▸
       at 1 2 (CS01 ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS10 c4) ▸
       at 0 2 (CS01 ∷ Sw23 ∷ []) (sym (c₂ (CS) (Swap))) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·23·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOXd(0;1;23;4) | CCZ013: 56 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ013 : Ws → ⟪ (Sb⁻0-1-23-4 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ013 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (run b6))))))
  where
  b0 : Chain (Sb⁻0-1-23-4 ∷ CCZ013 ∷ []) (CS03 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ Toff423 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CX13 ∷ CS03⁻ ∷ CCZ024 ∷ CX13 ∷ CS01 ∷ [])
  b0 = at 1 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl0333 (lit c4)) ▸
       at 0 1 (Sb⁻0-1-32-4 ∷ []) (lem-SBsymd-at0113203442 c4) ▸
       at 0 2 (CS03 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS20-at2332 c4) ▸
       at 1 1 (Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ Toff423 ∷ Bx⁻0-1324 ∷ []) (refl) ▸
       at 5 1 (Bx0-1324 ∷ []) (lem-BOXd-BOX-at2332 c4) ▸
       at 5 1 (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-beta-T-at2332 c4) ▸
       at 8 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 9 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0103 c4) ▸ done

  b1 : Chain (CS03 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ Toff423 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CX13 ∷ CS03⁻ ∷ CCZ024 ∷ CX13 ∷ CS01 ∷ []) (CS03 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ Toff423 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ Bx⁻0-1324 ∷ CS01 ∷ [])
  b1 = at 10 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 7 4 (CX13 ∷ CS03⁻ ∷ CX13 ∷ Toff013 ∷ []) (sym (wl0334 (lit c4))) ▸
       at 6 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 7 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0103 c4) ▸
       at 8 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 5 4 (CX13 ∷ CS03⁻ ∷ CX13 ∷ Toff013 ∷ []) (sym (wl0334 (lit c4))) ▸
       at 8 4 (Bx0-1324 ∷ []) (sym (lem-beta-T-at2332 c4)) ▸
       at 8 1 (Bx⁻0-1324 ∷ []) (sym (lem-BOXd-BOX-at2332 c4)) ▸ done

  b2 : Chain (CS03 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ Toff423 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ Bx⁻0-1324 ∷ CS01 ∷ []) (CS03 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ K4 ∷ CS24 ∷ CX32 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ K4⁻ ∷ Bx⁻0-1324 ∷ CS01 ∷ [])
  b2 = at 4 1 (K4 ∷ CCZ234 ∷ K4⁻ ∷ []) (sym (wl0335 (lit c4))) ▸
       at 6 4 (CX13 ∷ CS03⁻ ∷ CX13 ∷ K4⁻ ∷ []) (sym (wp0104 c4)) ▸
       at 5 1 (CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ []) (wl0336 (lit c4)) ▸
       at 9 4 (CX13 ∷ CS03⁻ ∷ CX13 ∷ CS34 ∷ []) (wp0105 c4) ▸
       at 8 4 (CX13 ∷ CS03⁻ ∷ CX13 ∷ CX32 ∷ []) (sym (wl0337 (lit c4))) ▸
       at 7 2 (CX13 ∷ CS24⁻ ∷ []) (wl0338 (lit c4)) ▸
       at 8 2 (CS03⁻ ∷ CS24⁻ ∷ []) (sym (wp0106 c4)) ▸
       at 9 2 (CX13 ∷ CS24⁻ ∷ []) (wl0338 (lit c4)) ▸ done

  b3 : Chain (CS03 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ K4 ∷ CS24 ∷ CX32 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ K4⁻ ∷ Bx⁻0-1324 ∷ CS01 ∷ []) (CS03 ∷ Sb0-1-4-2 ∷ Toff423 ∷ CS14⁻ ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ Toff423 ∷ Bx⁻0-1324 ∷ CS01 ∷ [])
  b3 = at 6 4 (CX13 ∷ CS03⁻ ∷ CX13 ∷ CX32 ∷ []) (sym (wl0337 (lit c4))) ▸
       at 5 2 (CX13 ∷ CS24 ∷ []) (wl0339 (lit c4)) ▸
       at 6 2 (CS03⁻ ∷ CS24 ∷ []) (sym (wp0107 c4)) ▸
       at 7 2 (CX13 ∷ CS24 ∷ []) (wl0339 (lit c4)) ▸
       at 8 5 (CCZ234 ∷ []) (sym (wl0336 (lit c4))) ▸
       at 4 4 (CX13 ∷ CS03⁻ ∷ CX13 ∷ K4 ∷ []) (sym (wp0108 c4)) ▸
       at 7 3 (Toff423 ∷ []) (wl0335 (lit c4)) ▸
       at 3 1 (CS14⁻ ∷ []) (refl) ▸ done

  b4 : Chain (CS03 ∷ Sb0-1-4-2 ∷ Toff423 ∷ CS14⁻ ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ Toff423 ∷ Bx⁻0-1324 ∷ CS01 ∷ []) (CS03 ∷ Sb0-1-4-2 ∷ K4 ∷ CS24 ∷ CX32 ∷ CX13 ∷ CS24⁻ ∷ CS03⁻ ∷ CX13 ∷ CX32 ∷ CS34 ∷ K4⁻ ∷ Sb⁻0-1-4-2 ∷ Toff423 ∷ Bx⁻0-1324 ∷ CS01 ∷ [])
  b4 = at 3 4 (CX13 ∷ CS03⁻ ∷ CX13 ∷ CS14⁻ ∷ []) (wp0109 c4) ▸
       at 6 1 (Sb⁻0-1-4-2 ∷ []) (refl) ▸
       at 2 1 (K4 ∷ CCZ234 ∷ K4⁻ ∷ []) (sym (wl0335 (lit c4))) ▸
       at 4 4 (CX13 ∷ CS03⁻ ∷ CX13 ∷ K4⁻ ∷ []) (sym (wp0104 c4)) ▸
       at 3 1 (CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ []) (wl0336 (lit c4)) ▸
       at 7 4 (CX13 ∷ CS03⁻ ∷ CX13 ∷ CS34 ∷ []) (wp0105 c4) ▸
       at 6 4 (CX13 ∷ CS03⁻ ∷ CX13 ∷ CX32 ∷ []) (sym (wl0337 (lit c4))) ▸
       at 5 2 (CX13 ∷ CS24⁻ ∷ []) (wl0338 (lit c4)) ▸ done

  b5 : Chain (CS03 ∷ Sb0-1-4-2 ∷ K4 ∷ CS24 ∷ CX32 ∷ CX13 ∷ CS24⁻ ∷ CS03⁻ ∷ CX13 ∷ CX32 ∷ CS34 ∷ K4⁻ ∷ Sb⁻0-1-4-2 ∷ Toff423 ∷ Bx⁻0-1324 ∷ CS01 ∷ []) (CS03 ∷ Sb0-1-4-2 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ K4 ∷ CCZ234 ∷ K4⁻ ∷ Sb⁻0-1-4-2 ∷ Toff423 ∷ Bx⁻0-1324 ∷ CS01 ∷ [])
  b5 = at 6 2 (CS03⁻ ∷ CS24⁻ ∷ []) (sym (wp0106 c4)) ▸
       at 7 2 (CX13 ∷ CS24⁻ ∷ []) (wl0338 (lit c4)) ▸
       at 4 4 (CX13 ∷ CS03⁻ ∷ CX13 ∷ CX32 ∷ []) (sym (wl0337 (lit c4))) ▸
       at 3 2 (CX13 ∷ CS24 ∷ []) (wl0339 (lit c4)) ▸
       at 4 2 (CS03⁻ ∷ CS24 ∷ []) (sym (wp0107 c4)) ▸
       at 5 2 (CX13 ∷ CS24 ∷ []) (wl0339 (lit c4)) ▸
       at 6 5 (CCZ234 ∷ []) (sym (wl0336 (lit c4))) ▸
       at 2 4 (CX13 ∷ CS03⁻ ∷ CX13 ∷ K4 ∷ []) (sym (wp0108 c4)) ▸ done

  b6 : Chain (CS03 ∷ Sb0-1-4-2 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ K4 ∷ CCZ234 ∷ K4⁻ ∷ Sb⁻0-1-4-2 ∷ Toff423 ∷ Bx⁻0-1324 ∷ CS01 ∷ []) (CCZ013 ∷ Sb⁻0-1-23-4 ∷ [])
  b6 = at 5 3 (Toff423 ∷ []) (wl0335 (lit c4)) ▸
       at 1 1 (CS14 ∷ []) (refl) ▸
       at 1 4 (CX13 ∷ CS03⁻ ∷ CX13 ∷ CS14 ∷ []) (wp0110 c4) ▸
       at 4 1 (Sb0-1-4-2 ∷ []) (refl) ▸
       at 4 5 (Sb⁻0-1-32-4 ∷ []) (refl) ▸
       at 4 2 (CS01 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS10-at2332 c4) ▸
       at 5 1 (Sb⁻0-1-23-4 ∷ []) (sym (lem-SBsymd-at0113203442 c4)) ▸
       at 0 5 (CCZ013 ∷ []) (sym (wl0333 (lit c4))) ▸ done


-- auto SBOXd(0;1;23;4) | Kd0: 11 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-Kd0 : Ws → ⟪ (Sb⁻0-1-23-4 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-Kd0 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb⁻0-1-23-4 ∷ K0⁻ ∷ []) (CS14 ∷ K0⁻ ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ [])
  b0 = at 0 1 (Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) (refl) ▸
       at 4 2 (K0⁻ ∷ Bx⁻0-1234 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-Kd0 c4) ▸
       at 3 2 (K0⁻ ∷ Toff423 ∷ []) (sym (wl0340 (lit c4))) ▸
       at 2 1 (CS14⁻ ∷ []) (refl) ▸
       at 2 2 (K0⁻ ∷ CS14⁻ ∷ []) (wp0111 c4) ▸
       at 3 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 1 2 (K0⁻ ∷ Toff423 ∷ []) (sym (wl0340 (lit c4))) ▸
       at 0 1 (CS14 ∷ []) (refl) ▸ done

  b1 : Chain (CS14 ∷ K0⁻ ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) (K0⁻ ∷ Sb⁻0-1-23-4 ∷ [])
  b1 = at 0 2 (K0⁻ ∷ CS14 ∷ []) (wp0112 c4) ▸
       at 1 1 (Sb0-1-4-3 ∷ []) (refl) ▸
       at 1 5 (Sb⁻0-1-23-4 ∷ []) (refl) ▸ done


-- auto SBOXd(0;1;23;4) | K0 @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-K0-at2332 : Ws → ⟪ (Sb⁻0-1-32-4 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-K0-at2332 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-32-4 ∷ K0 ∷ []) (K0 ∷ Sb⁻0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb⁻0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 1 2 (K0 ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-K0 c4) ▸
       at 0 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·23·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOXd(0;1;23;4) | CCZ013 @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ013-at2332 : Ws → ⟪ (Sb⁻0-1-32-4 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ013-at2332 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-32-4 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sb⁻0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb⁻0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 (lit c4)) ▸
       at 1 2 (CCZ013 ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ013 c4) ▸
       at 0 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 (lit c4)) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·23·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOXd(0;1;23;4) | Kd0 @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-Kd0-at2332 : Ws → ⟪ (Sb⁻0-1-32-4 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-Kd0-at2332 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-32-4 ∷ K0⁻ ∷ []) (K0⁻ ∷ Sb⁻0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb⁻0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 (K0⁻ ∷ Sw23 ∷ []) (sym (c₁ (K • iI) (Swap ↑))) ▸
       at 1 2 (K0⁻ ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-Kd0 c4) ▸
       at 0 2 (K0⁻ ∷ Sw23 ∷ []) (sym (c₁ (K • iI) (Swap ↑))) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·23·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOXd(0;1;23;4) | TOFF012: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF012 : Ws → ⟪ (Sb⁻0-1-23-4 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF012 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-23-4 ∷ Toff012 ∷ []) (Toff012 ∷ Sb⁻0-1-23-4 ∷ [])
  b0 = at 1 1 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (sym (wl0341 (lit c4))) ▸
       at 0 1 (Sb⁻0-1-32-4 ∷ []) (lem-SBsymd-at0113203442 c4) ▸
       at 0 2 (K0 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-K0-at2332 c4) ▸
       at 1 2 (CCZ012 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ013-at2332 c4) ▸
       at 2 2 (K0⁻ ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-Kd0-at2332 c4) ▸
       at 3 1 (Sb⁻0-1-23-4 ∷ []) (sym (lem-SBsymd-at0113203442 c4)) ▸
       at 0 3 (Toff012 ∷ []) (wl0341 (lit c4)) ▸ done


-- CS20-beta-c @2332: 7 steps
lem-CS20-beta-c-at2332 : Ws → ⟪ (CS03 ∷ Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ CS03 ∷ []) ⟫ʷ
lem-CS20-beta-c-at2332 c4 = run b0
  where
  b0 : Chain (CS03 ∷ Bx0-1324 ∷ []) (Bx0-1324 ∷ CS03 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (CS02 ∷ Sw23 ∷ []) (lem-nat-2-CS03 (lit c4)) ▸
       at 2 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ (lit c4)) ▸
       at 1 2 (Bx0-1234 ∷ CS02 ∷ []) (lem-CS20-beta-c c4) ▸
       at 0 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ (lit c4)) ▸
       at 1 2 (CS03 ∷ Sw23 ∷ []) (lem-nat-2-CS02 (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- CS20-beta-c @243243: 7 steps
lem-CS20-beta-c-at243243 : Ws → ⟪ (CS04 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CS04 ∷ []) ⟫ʷ
lem-CS20-beta-c-at243243 c4 = run b0
  where
  b0 : Chain (CS04 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CS04 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (CS03 ∷ Sw34 ∷ []) (lem-nat-3-CS04 (lit c4)) ▸
       at 2 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ (lit c4)) ▸
       at 1 2 (Bx0-1324 ∷ CS03 ∷ []) (lem-CS20-beta-c-at2332 c4) ▸
       at 0 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ (lit c4)) ▸
       at 1 2 (CS04 ∷ Sw34 ∷ []) (lem-nat-3-CS03 (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto BOXd(0;1234) | CS40: 9 steps
lem-auto-BOXd⟨0·1234⟩-∣-CS40 : Ws → ⟪ (Bx⁻0-1234 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ Bx⁻0-1234 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CS40 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx⁻0-1234 ∷ CS04 ∷ []) (CS04 ∷ Bx0-1234 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ []) (lem-BOXd-BOX c4) ▸
       at 1 1 (CS04 ∷ []) (wp0113 c4) ▸
       at 0 1 (Bx0-1243 ∷ []) (lem-sym34 c4) ▸
       at 0 1 (Bx0-1423 ∷ []) (lem-sym23-at3443 c4) ▸
       at 0 2 (CS04 ∷ Bx0-1423 ∷ []) (sym (lem-CS20-beta-c-at243243 c4)) ▸
       at 1 1 (Bx0-1243 ∷ []) (lem-sym23-at243243 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym34-at3443 c4) ▸
       at 0 1 (CS04 ∷ []) (wp0113 c4) ▸ done

  b1 : Chain (CS04 ∷ Bx0-1234 ∷ []) (CS04 ∷ Bx⁻0-1234 ∷ [])
  b1 = at 1 1 (Bx⁻0-1234 ∷ []) (sym (lem-BOXd-BOX c4)) ▸ done


-- CS20-beta-ci @2332: 7 steps
lem-CS20-beta-ci-at2332 : Ws → ⟪ (CS03⁻ ∷ Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-CS20-beta-ci-at2332 c4 = run b0
  where
  b0 : Chain (CS03⁻ ∷ Bx0-1324 ∷ []) (Bx0-1324 ∷ CS03⁻ ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (CS02⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd03 (lit c4)) ▸
       at 2 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ (lit c4)) ▸
       at 1 2 (Bx0-1234 ∷ CS02⁻ ∷ []) (lem-CS20-beta-ci c4) ▸
       at 0 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ (lit c4)) ▸
       at 1 2 (CS03⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd02 (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- CS20-beta-ci @243243: 7 steps
lem-CS20-beta-ci-at243243 : Ws → ⟪ (CS04⁻ ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CS04⁻ ∷ []) ⟫ʷ
lem-CS20-beta-ci-at243243 c4 = run b0
  where
  b0 : Chain (CS04⁻ ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CS04⁻ ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (CS03⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd04 (lit c4)) ▸
       at 2 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ (lit c4)) ▸
       at 1 2 (Bx0-1324 ∷ CS03⁻ ∷ []) (lem-CS20-beta-ci-at2332 c4) ▸
       at 0 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ (lit c4)) ▸
       at 1 2 (CS04⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd03 (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto BOXd(0;1234) | CSd40: 9 steps
lem-auto-BOXd⟨0·1234⟩-∣-CSd40 : Ws → ⟪ (Bx⁻0-1234 ∷ CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS04⁻ ∷ Bx⁻0-1234 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CSd40 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx⁻0-1234 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ Bx0-1234 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ []) (lem-BOXd-BOX c4) ▸
       at 1 1 (CS04⁻ ∷ []) (wp0114 c4) ▸
       at 0 1 (Bx0-1243 ∷ []) (lem-sym34 c4) ▸
       at 0 1 (Bx0-1423 ∷ []) (lem-sym23-at3443 c4) ▸
       at 0 2 (CS04⁻ ∷ Bx0-1423 ∷ []) (sym (lem-CS20-beta-ci-at243243 c4)) ▸
       at 1 1 (Bx0-1243 ∷ []) (lem-sym23-at243243 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym34-at3443 c4) ▸
       at 0 1 (CS04⁻ ∷ []) (wp0114 c4) ▸ done

  b1 : Chain (CS04⁻ ∷ Bx0-1234 ∷ []) (CS04⁻ ∷ Bx⁻0-1234 ∷ [])
  b1 = at 1 1 (Bx⁻0-1234 ∷ []) (sym (lem-BOXd-BOX c4)) ▸ done


-- auto CCZ012 | BOX(3;0142): 1 steps
lem-auto-CCZ012-∣-BOX⟨3·0142⟩ : Ws → ⟪ (CCZ012 ∷ Bx3-0142 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0142 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·0142⟩ c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Bx3-0142 ∷ []) (Bx3-0142 ∷ CCZ012 ∷ [])
  b0 = at 0 2 (Bx3-0142 ∷ CCZ012 ∷ []) (lem-c124-beta-at0310213442 c4) ▸ done


-- auto SBOX(0;1;23;4) | K0: 11 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-K0 : Ws → ⟪ (Sb0-1-23-4 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-K0 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-23-4 ∷ K0 ∷ []) (Bx0-1234 ∷ Toff423 ∷ K0 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 1 (CS14⁻ ∷ []) (refl) ▸
       at 4 2 (K0 ∷ CS14⁻ ∷ []) (wp0096 c4) ▸
       at 5 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 3 2 (K0 ∷ Toff423 ∷ []) (sym (wl0330 (lit c4))) ▸
       at 2 1 (CS14 ∷ []) (refl) ▸
       at 2 2 (K0 ∷ CS14 ∷ []) (wp0097 c4) ▸
       at 3 1 (Sb0-1-4-3 ∷ []) (refl) ▸ done

  b1 : Chain (Bx0-1234 ∷ Toff423 ∷ K0 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (K0 ∷ Sb0-1-23-4 ∷ [])
  b1 = at 1 2 (K0 ∷ Toff423 ∷ []) (sym (wl0330 (lit c4))) ▸
       at 0 2 (K0 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-K0 c4) ▸
       at 1 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- auto BOX(0;1234) | CS30: 5 steps
lem-auto-BOX⟨0·1234⟩-∣-CS30 : Ws → ⟪ (Bx0-1234 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS30 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CS03 ∷ []) (CS03 ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (CS03 ∷ []) (wl0342 (lit c4)) ▸
       at 0 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 0 2 (CS03 ∷ Bx0-1324 ∷ []) (sym (lem-CS20-beta-c-at2332 c4)) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸
       at 0 1 (CS03 ∷ []) (wl0342 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | CS30: 11 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS30 : Ws → ⟪ (Sb0-1-23-4 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS30 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-23-4 ∷ CS03 ∷ []) (Bx0-1234 ∷ Toff423 ∷ CS03 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 1 (CS14⁻ ∷ []) (refl) ▸
       at 4 2 (CS03 ∷ CS14⁻ ∷ []) (sym (wp0115 c4)) ▸
       at 5 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 3 2 (CS03 ∷ Toff423 ∷ []) (sym (wp0116 c4)) ▸
       at 2 1 (CS14 ∷ []) (refl) ▸
       at 2 2 (CS03 ∷ CS14 ∷ []) (sym (wp0117 c4)) ▸
       at 3 1 (Sb0-1-4-3 ∷ []) (refl) ▸ done

  b1 : Chain (Bx0-1234 ∷ Toff423 ∷ CS03 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (CS03 ∷ Sb0-1-23-4 ∷ [])
  b1 = at 1 2 (CS03 ∷ Toff423 ∷ []) (sym (wp0116 c4)) ▸
       at 0 2 (CS03 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS30 c4) ▸
       at 1 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- auto BOX(0;1234) | CCZ214: 3 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ214 : Ws → ⟪ (Bx0-1234 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ214 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ []) (wl0343 (lit c4)) ▸
       at 0 2 (CCZ124 ∷ Bx0-1234 ∷ []) (sym (lem-c124-beta c4)) ▸
       at 0 1 (CCZ124 ∷ []) (wl0343 (lit c4)) ▸ done


-- auto BOX(0;1234) | CS10: 5 steps
lem-auto-BOX⟨0·1234⟩-∣-CS10 : Ws → ⟪ (Bx0-1234 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS10 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CS01 ∷ []) (CS01 ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (CS01 ∷ []) (wl0332 (lit c4)) ▸
       at 0 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 0 2 (CS01 ∷ Bx0-2134 ∷ []) (sym (lem-CS20-beta-c-at1221 c4)) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸
       at 0 1 (CS01 ∷ []) (wl0332 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | CS10: 11 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS10 : Ws → ⟪ (Sb0-1-23-4 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS10 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-23-4 ∷ CS01 ∷ []) (Bx0-1234 ∷ Toff423 ∷ CS01 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 1 (CS14⁻ ∷ []) (refl) ▸
       at 4 2 (CS01 ∷ CS14⁻ ∷ []) (sym (wp0101 c4)) ▸
       at 5 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 3 2 (CS01 ∷ Toff423 ∷ []) (lem-auto-TOFF012-∣-CS34-at0412233140 c4) ▸
       at 2 1 (CS14 ∷ []) (refl) ▸
       at 2 2 (CS01 ∷ CS14 ∷ []) (sym (wp0102 c4)) ▸
       at 3 1 (Sb0-1-4-3 ∷ []) (refl) ▸ done

  b1 : Chain (Bx0-1234 ∷ Toff423 ∷ CS01 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (CS01 ∷ Sb0-1-23-4 ∷ [])
  b1 = at 1 2 (CS01 ∷ Toff423 ∷ []) (lem-auto-TOFF012-∣-CS34-at0412233140 c4) ▸
       at 0 2 (CS01 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS10 c4) ▸
       at 1 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- auto SBOX(0;1;23;4) | CS30 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS30-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS30-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CS02 ∷ []) (CS02 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 (CS03 ∷ Sw23 ∷ []) (lem-nat-2-CS02 (lit c4)) ▸
       at 1 2 (CS03 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS30 c4) ▸
       at 0 2 (CS02 ∷ Sw23 ∷ []) (lem-nat-2-CS03 (lit c4)) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- CX23-beta @1221: 8 steps
lem-CX23-beta-at1221 : Ws → ⟪ (CX13 ∷ Bx0-2134 ∷ CX13 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CX23-beta-at1221 c4 = run b0
  where
  b0 : Chain (CX13 ∷ Bx0-2134 ∷ CX13 ∷ []) (Bx0-2134 ∷ CCZ124 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CX23 ∷ Sw12 ∷ []) (sym (wl0052 (lit c4))) ▸
       at 2 2 (Bx0-1234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2134⟩ (lit c4)) ▸
       at 3 2 (CX23 ∷ Sw12 ∷ []) (sym (wl0052 (lit c4))) ▸
       at 1 3 (Bx0-1234 ∷ CCZ124 ∷ []) (lem-CX23-beta c4) ▸
       at 0 2 (Bx0-2134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1234⟩ (lit c4)) ▸
       at 1 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0078 (lit c4))) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ214 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ214-at2332 : Ws → ⟪ (Bx0-1324 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ214-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ CCZ134 ∷ []) (CCZ134 ∷ Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ (lit c4)) ▸
       at 2 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 (lit c4)) ▸
       at 1 2 (CCZ124 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ214 c4) ▸
       at 0 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 (lit c4)) ▸
       at 1 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | CS10 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS10-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS10-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CS01 ∷ []) (CS01 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 (CS01 ∷ Sw23 ∷ []) (sym (c₂ (CS) (Swap))) ▸
       at 1 2 (CS01 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS10 c4) ▸
       at 0 2 (CS01 ∷ Sw23 ∷ []) (sym (c₂ (CS) (Swap))) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | Kd0: 11 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd0 : Ws → ⟪ (Sb0-1-23-4 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd0 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-23-4 ∷ K0⁻ ∷ []) (Bx0-1234 ∷ Toff423 ∷ K0⁻ ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 1 (CS14⁻ ∷ []) (refl) ▸
       at 4 2 (K0⁻ ∷ CS14⁻ ∷ []) (wp0111 c4) ▸
       at 5 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 3 2 (K0⁻ ∷ Toff423 ∷ []) (sym (wl0340 (lit c4))) ▸
       at 2 1 (CS14 ∷ []) (refl) ▸
       at 2 2 (K0⁻ ∷ CS14 ∷ []) (wp0112 c4) ▸
       at 3 1 (Sb0-1-4-3 ∷ []) (refl) ▸ done

  b1 : Chain (Bx0-1234 ∷ Toff423 ∷ K0⁻ ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (K0⁻ ∷ Sb0-1-23-4 ∷ [])
  b1 = at 1 2 (K0⁻ ∷ Toff423 ∷ []) (sym (wl0340 (lit c4))) ▸
       at 0 2 (K0⁻ ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-Kd0 c4) ▸
       at 1 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- auto SBOX(0;1;23;4) | K0 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ K0 ∷ []) (K0 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 1 2 (K0 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K0 c4) ▸
       at 0 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | Kd0 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd0-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd0-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ K0⁻ ∷ []) (K0⁻ ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 (K0⁻ ∷ Sw23 ∷ []) (sym (c₁ (K • iI) (Swap ↑))) ▸
       at 1 2 (K0⁻ ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd0 c4) ▸
       at 0 2 (K0⁻ ∷ Sw23 ∷ []) (sym (c₁ (K • iI) (Swap ↑))) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- CS12-beta @13243142: 7 steps
lem-CS12-beta-at13243142 : Ws → ⟪ (CS34 ∷ Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ CS34 ∷ []) ⟫ʷ
lem-CS12-beta-at13243142 c4 = run b0
  where
  b0 : Chain (CS34 ∷ Bx0-3412 ∷ []) (Bx0-3412 ∷ CS34 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0015 (lit c4))) ▸
       at 2 2 (Bx0-2413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3412⟩ (lit c4)) ▸
       at 1 2 (Bx0-2413 ∷ CS24 ∷ []) (lem-CS12-beta-at12243143 c4) ▸
       at 0 2 (Bx0-3412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2413⟩ (lit c4)) ▸
       at 1 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0011 (lit c4))) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto BOX(0;1234) | CS43: 11 steps
lem-auto-BOX⟨0·1234⟩-∣-CS43 : Ws → ⟪ (Bx0-1234 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS43 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-1234 ∷ CS34 ∷ []) (CS34 ∷ Bx0-3124 ∷ [])
  b0 = at 1 1 (CS34 ∷ []) (wl0344 (lit c4)) ▸
       at 0 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 0 1 (Bx0-1342 ∷ []) (lem-sym34-at2332 c4) ▸
       at 0 1 (Bx0-3142 ∷ []) (lem-sym12-at233442 c4) ▸
       at 0 1 (Bx0-3412 ∷ []) (lem-sym23-at13213442 c4) ▸
       at 0 2 (CS34 ∷ Bx0-3412 ∷ []) (sym (lem-CS12-beta-at13243142 c4)) ▸
       at 1 1 (Bx0-3142 ∷ []) (lem-sym23-at13243142 c4) ▸
       at 1 1 (Bx0-3124 ∷ []) (lem-sym34-at13213442 c4) ▸ done

  b1 : Chain (CS34 ∷ Bx0-3124 ∷ []) (CS34 ∷ Bx0-1234 ∷ [])
  b1 = at 1 1 (Bx0-1324 ∷ []) (lem-sym12-at132132 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸
       at 0 1 (CS34 ∷ []) (wl0344 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | CS43: 9 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS43 : Ws → ⟪ (Sb0-1-23-4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS43 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-23-4 ∷ CS34 ∷ []) (CS34 ∷ Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 1 (CS14⁻ ∷ []) (refl) ▸
       at 4 2 (CS34 ∷ CS14⁻ ∷ []) (wl0345 (lit c4)) ▸
       at 5 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 2 1 (CS14 ∷ []) (refl) ▸
       at 1 4 (CS34 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ []) (sym (wl0346 (lit c4))) ▸
       at 3 1 (Sb0-1-4-3 ∷ []) (refl) ▸
       at 0 2 (CS34 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS43 c4) ▸ done

  b1 : Chain (CS34 ∷ Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (CS34 ∷ Sb0-1-23-4 ∷ [])
  b1 = at 1 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- auto BOX(0;1234) | CS34: 9 steps
lem-auto-BOX⟨0·1234⟩-∣-CS34 : Ws → ⟪ (Bx0-1234 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS34 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-1234 ∷ CS34 ∷ []) (CS34 ∷ Bx0-1324 ∷ [])
  b0 = at 0 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 0 1 (Bx0-1342 ∷ []) (lem-sym34-at2332 c4) ▸
       at 0 1 (Bx0-3142 ∷ []) (lem-sym12-at233442 c4) ▸
       at 0 1 (Bx0-3412 ∷ []) (lem-sym23-at13213442 c4) ▸
       at 0 2 (CS34 ∷ Bx0-3412 ∷ []) (sym (lem-CS12-beta-at13243142 c4)) ▸
       at 1 1 (Bx0-3142 ∷ []) (lem-sym23-at13243142 c4) ▸
       at 1 1 (Bx0-3124 ∷ []) (lem-sym34-at13213442 c4) ▸
       at 1 1 (Bx0-1324 ∷ []) (lem-sym12-at132132 c4) ▸ done

  b1 : Chain (CS34 ∷ Bx0-1324 ∷ []) (CS34 ∷ Bx0-1234 ∷ [])
  b1 = at 1 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸ done


-- auto SBOX(0;1;23;4) | CS34: 9 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS34 : Ws → ⟪ (Sb0-1-23-4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS34 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-23-4 ∷ CS34 ∷ []) (CS34 ∷ Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 1 (CS14⁻ ∷ []) (refl) ▸
       at 4 2 (CS34 ∷ CS14⁻ ∷ []) (wl0345 (lit c4)) ▸
       at 5 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 2 1 (CS14 ∷ []) (refl) ▸
       at 1 4 (CS34 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ []) (sym (wl0346 (lit c4))) ▸
       at 3 1 (Sb0-1-4-3 ∷ []) (refl) ▸
       at 0 2 (CS34 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS34 c4) ▸ done

  b1 : Chain (CS34 ∷ Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (CS34 ∷ Sb0-1-23-4 ∷ [])
  b1 = at 1 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- auto BOX(0;1234) | CS20: 3 steps
lem-auto-BOX⟨0·1234⟩-∣-CS20 : Ws → ⟪ (Bx0-1234 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS20 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CS02 ∷ []) (CS02 ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (CS02 ∷ []) (wl0331 (lit c4)) ▸
       at 0 2 (CS02 ∷ Bx0-1234 ∷ []) (sym (lem-CS20-beta-c c4)) ▸
       at 0 1 (CS02 ∷ []) (wl0331 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | CS20: 11 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS20 : Ws → ⟪ (Sb0-1-23-4 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS20 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-23-4 ∷ CS02 ∷ []) (Bx0-1234 ∷ Toff423 ∷ CS02 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 1 (CS14⁻ ∷ []) (refl) ▸
       at 4 2 (CS02 ∷ CS14⁻ ∷ []) (sym (wp0099 c4)) ▸
       at 5 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 3 2 (CS02 ∷ Toff423 ∷ []) (sym (wp0098 c4)) ▸
       at 2 1 (CS14 ∷ []) (refl) ▸
       at 2 2 (CS02 ∷ CS14 ∷ []) (sym (wp0100 c4)) ▸
       at 3 1 (Sb0-1-4-3 ∷ []) (refl) ▸ done

  b1 : Chain (Bx0-1234 ∷ Toff423 ∷ CS02 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (CS02 ∷ Sb0-1-23-4 ∷ [])
  b1 = at 1 2 (CS02 ∷ Toff423 ∷ []) (sym (wp0098 c4)) ▸
       at 0 2 (CS02 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS20 c4) ▸
       at 1 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- auto BOX(0;1234) | CCZ314: 5 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ314 : Ws → ⟪ (Bx0-1234 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ314 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CCZ134 ∷ []) (CCZ134 ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ []) (wl0347 (lit c4)) ▸
       at 0 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 0 2 (CCZ134 ∷ Bx0-1324 ∷ []) (sym (lem-c124-beta-at2332 c4)) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸
       at 0 1 (CCZ134 ∷ []) (wl0347 (lit c4)) ▸ done


-- auto BOX(0;1234) | CSd20: 3 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd20 : Ws → ⟪ (Bx0-1234 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd20 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (CS02⁻ ∷ []) (wl0348 (lit c4)) ▸
       at 0 2 (CS02⁻ ∷ Bx0-1234 ∷ []) (sym (lem-CS20-beta-ci c4)) ▸
       at 0 1 (CS02⁻ ∷ []) (wl0348 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | CS20 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS20-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS20-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CS03 ∷ []) (CS03 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 (CS02 ∷ Sw23 ∷ []) (lem-nat-2-CS03 (lit c4)) ▸
       at 1 2 (CS02 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS20 c4) ▸
       at 0 2 (CS03 ∷ Sw23 ∷ []) (lem-nat-2-CS02 (lit c4)) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ314 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ314-at2332 : Ws → ⟪ (Bx0-1324 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ314-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ (lit c4)) ▸
       at 2 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 (lit c4)) ▸
       at 1 2 (CCZ134 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ314 c4) ▸
       at 0 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 (lit c4)) ▸
       at 1 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto BOX(0;1234) | CSd20 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd20-at2332 : Ws → ⟪ (Bx0-1324 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd20-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ (lit c4)) ▸
       at 2 2 (CS02⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd03 (lit c4)) ▸
       at 1 2 (CS02⁻ ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd20 c4) ▸
       at 0 2 (CS03⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd02 (lit c4)) ▸
       at 1 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | CCZ013: 64 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ013 : Ws → ⟪ (Sb0-1-23-4 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ013 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (Sb0-1-23-4 ∷ CCZ013 ∷ []) (CS03 ∷ Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ K4 ∷ CCZ234 ∷ K4⁻ ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ Sb⁻0-1-4-2 ∷ CS01 ∷ [])
  b0 = at 1 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl0333 (lit c4)) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS03 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS20-at2332 c4) ▸
       at 1 1 (Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ []) (refl) ▸
       at 5 1 (CS14⁻ ∷ []) (refl) ▸
       at 5 4 (CX13 ∷ CS03⁻ ∷ CX13 ∷ CS14⁻ ∷ []) (wp0109 c4) ▸
       at 8 1 (Sb⁻0-1-4-2 ∷ []) (refl) ▸
       at 4 1 (K4 ∷ CCZ234 ∷ K4⁻ ∷ []) (sym (wl0335 (lit c4))) ▸ done

  b1 : Chain (CS03 ∷ Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ K4 ∷ CCZ234 ∷ K4⁻ ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ Sb⁻0-1-4-2 ∷ CS01 ∷ []) (CS03 ∷ Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ K4 ∷ CS24 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ K4⁻ ∷ Sb⁻0-1-4-2 ∷ CS01 ∷ [])
  b1 = at 6 4 (CX13 ∷ CS03⁻ ∷ CX13 ∷ K4⁻ ∷ []) (sym (wp0104 c4)) ▸
       at 5 1 (CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ []) (wl0336 (lit c4)) ▸
       at 9 4 (CX13 ∷ CS03⁻ ∷ CX13 ∷ CS34 ∷ []) (wp0105 c4) ▸
       at 8 4 (CX13 ∷ CS03⁻ ∷ CX13 ∷ CX32 ∷ []) (sym (wl0337 (lit c4))) ▸
       at 7 2 (CX13 ∷ CS24⁻ ∷ []) (wl0338 (lit c4)) ▸
       at 8 2 (CS03⁻ ∷ CS24⁻ ∷ []) (sym (wp0106 c4)) ▸
       at 9 2 (CX13 ∷ CS24⁻ ∷ []) (wl0338 (lit c4)) ▸
       at 6 4 (CX13 ∷ CS03⁻ ∷ CX13 ∷ CX32 ∷ []) (sym (wl0337 (lit c4))) ▸ done

  b2 : Chain (CS03 ∷ Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ K4 ∷ CS24 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ K4⁻ ∷ Sb⁻0-1-4-2 ∷ CS01 ∷ []) (CS03 ∷ Bx0-1324 ∷ Toff423 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS14 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS01 ∷ [])
  b2 = at 5 2 (CX13 ∷ CS24 ∷ []) (wl0339 (lit c4)) ▸
       at 6 2 (CS03⁻ ∷ CS24 ∷ []) (sym (wp0107 c4)) ▸
       at 7 2 (CX13 ∷ CS24 ∷ []) (wl0339 (lit c4)) ▸
       at 8 5 (CCZ234 ∷ []) (sym (wl0336 (lit c4))) ▸
       at 4 4 (CX13 ∷ CS03⁻ ∷ CX13 ∷ K4 ∷ []) (sym (wp0108 c4)) ▸
       at 7 3 (Toff423 ∷ []) (wl0335 (lit c4)) ▸
       at 3 1 (CS14 ∷ []) (refl) ▸
       at 3 4 (CX13 ∷ CS03⁻ ∷ CX13 ∷ CS14 ∷ []) (wp0110 c4) ▸ done

  b3 : Chain (CS03 ∷ Bx0-1324 ∷ Toff423 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS14 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS01 ∷ []) (CS03 ∷ Bx0-1324 ∷ K4 ∷ CS24 ∷ CX32 ∷ CX13 ∷ CS03⁻ ∷ CS24⁻ ∷ CX13 ∷ CX32 ∷ CS34 ∷ K4⁻ ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS01 ∷ [])
  b3 = at 6 1 (Sb0-1-4-2 ∷ []) (refl) ▸
       at 2 1 (K4 ∷ CCZ234 ∷ K4⁻ ∷ []) (sym (wl0335 (lit c4))) ▸
       at 4 4 (CX13 ∷ CS03⁻ ∷ CX13 ∷ K4⁻ ∷ []) (sym (wp0104 c4)) ▸
       at 3 1 (CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ []) (wl0336 (lit c4)) ▸
       at 7 4 (CX13 ∷ CS03⁻ ∷ CX13 ∷ CS34 ∷ []) (wp0105 c4) ▸
       at 6 4 (CX13 ∷ CS03⁻ ∷ CX13 ∷ CX32 ∷ []) (sym (wl0337 (lit c4))) ▸
       at 5 2 (CX13 ∷ CS24⁻ ∷ []) (wl0338 (lit c4)) ▸
       at 6 2 (CS03⁻ ∷ CS24⁻ ∷ []) (sym (wp0106 c4)) ▸ done

  b4 : Chain (CS03 ∷ Bx0-1324 ∷ K4 ∷ CS24 ∷ CX32 ∷ CX13 ∷ CS03⁻ ∷ CS24⁻ ∷ CX13 ∷ CX32 ∷ CS34 ∷ K4⁻ ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS01 ∷ []) (CS03 ∷ Bx0-1324 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS01 ∷ [])
  b4 = at 7 2 (CX13 ∷ CS24⁻ ∷ []) (wl0338 (lit c4)) ▸
       at 4 4 (CX13 ∷ CS03⁻ ∷ CX13 ∷ CX32 ∷ []) (sym (wl0337 (lit c4))) ▸
       at 3 2 (CX13 ∷ CS24 ∷ []) (wl0339 (lit c4)) ▸
       at 4 2 (CS03⁻ ∷ CS24 ∷ []) (sym (wp0107 c4)) ▸
       at 5 2 (CX13 ∷ CS24 ∷ []) (wl0339 (lit c4)) ▸
       at 6 5 (CCZ234 ∷ []) (sym (wl0336 (lit c4))) ▸
       at 2 4 (CX13 ∷ CS03⁻ ∷ CX13 ∷ K4 ∷ []) (sym (wp0108 c4)) ▸
       at 5 3 (Toff423 ∷ []) (wl0335 (lit c4)) ▸ done

  b5 : Chain (CS03 ∷ Bx0-1324 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS01 ∷ []) (CS03 ∷ CX13 ∷ CCZ124 ∷ CS03⁻ ∷ Bx0-1324 ∷ CX13 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS01 ∷ [])
  b5 = at 1 0 (CX13 ∷ CX13 ∷ []) (sym (wl0349 (lit c4))) ▸
       at 3 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸
       at 3 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 2 3 (Bx0-2134 ∷ CCZ124 ∷ []) (lem-CX23-beta-at1221 c4) ▸
       at 2 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸
       at 2 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 2 2 (CCZ124 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ314-at2332 c4) ▸
       at 3 2 (CS03⁻ ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd20-at2332 c4) ▸ done

  b6 : Chain (CS03 ∷ CX13 ∷ CCZ124 ∷ CS03⁻ ∷ Bx0-1324 ∷ CX13 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS01 ∷ []) (CS03 ∷ CCZ124 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CCZ124 ∷ Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS01 ∷ [])
  b6 = at 4 0 (CX13 ∷ CX13 ∷ []) (sym (wl0349 (lit c4))) ▸
       at 6 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸
       at 6 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 5 3 (Bx0-2134 ∷ CCZ124 ∷ []) (lem-CX23-beta-at1221 c4) ▸
       at 5 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸
       at 5 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 5 2 (CCZ124 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ314-at2332 c4) ▸
       at 1 2 (CCZ124 ∷ CX13 ∷ []) (sym (wl0350 (lit c4))) ▸ done

  b7 : Chain (CS03 ∷ CCZ124 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CCZ124 ∷ Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS01 ∷ []) (CCZ013 ∷ Sb0-1-23-4 ∷ [])
  b7 = at 4 2 (CCZ124 ∷ CX13 ∷ []) (sym (wl0350 (lit c4))) ▸
       at 3 2 (CCZ124 ∷ CS03⁻ ∷ []) (lem-comm-CSd03-CCZ124 (lit c4)) ▸
       at 2 2 (CCZ124 ∷ CX13 ∷ []) (sym (wl0350 (lit c4))) ▸
       at 1 2 [] (wl0351 (lit c4)) ▸
       at 4 5 (Sb0-1-32-4 ∷ []) (refl) ▸
       at 4 2 (CS01 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS10-at2332 c4) ▸
       at 5 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 5 (CCZ013 ∷ []) (sym (wl0333 (lit c4))) ▸ done


-- auto SBOX(0;1;23;4) | CCZ013 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ013-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ013-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 (lit c4)) ▸
       at 1 2 (CCZ013 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ013 c4) ▸
       at 0 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 (lit c4)) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | TOFF012: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF012 : Ws → ⟪ (Sb0-1-23-4 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF012 c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ Toff012 ∷ []) (Toff012 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 1 1 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (sym (wl0341 (lit c4))) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (K0 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at2332 c4) ▸
       at 1 2 (CCZ012 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ013-at2332 c4) ▸
       at 2 2 (K0⁻ ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd0-at2332 c4) ▸
       at 3 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 3 (Toff012 ∷ []) (wl0341 (lit c4)) ▸ done


-- auto BOX(0;1234) | CS42: 9 steps
lem-auto-BOX⟨0·1234⟩-∣-CS42 : Ws → ⟪ (Bx0-1234 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS42 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-1234 ∷ CS24 ∷ []) (CS24 ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (CS24 ∷ []) (wl0352 (lit c4)) ▸
       at 0 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 0 1 (Bx0-2143 ∷ []) (lem-sym34-at1221 c4) ▸
       at 0 1 (Bx0-2413 ∷ []) (lem-sym23-at12213443 c4) ▸
       at 0 2 (CS24 ∷ Bx0-2413 ∷ []) (sym (lem-CS12-beta-at12243143 c4)) ▸
       at 1 1 (Bx0-2143 ∷ []) (lem-sym23-at12243143 c4) ▸
       at 1 1 (Bx0-2134 ∷ []) (lem-sym34-at12213443 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸ done

  b1 : Chain (CS24 ∷ Bx0-1234 ∷ []) (CS24 ∷ Bx0-1234 ∷ [])
  b1 = at 0 1 (CS24 ∷ []) (wl0352 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | CS42: 9 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS42 : Ws → ⟪ (Sb0-1-23-4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS42 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-23-4 ∷ CS24 ∷ []) (CS24 ∷ Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 1 (CS14⁻ ∷ []) (refl) ▸
       at 4 2 (CS24 ∷ CS14⁻ ∷ []) (wl0303 (lit c4)) ▸
       at 5 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 2 1 (CS14 ∷ []) (refl) ▸
       at 1 4 (CS24 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ []) (sym (wl0304 (lit c4))) ▸
       at 3 1 (Sb0-1-4-3 ∷ []) (refl) ▸
       at 0 2 (CS24 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS42 c4) ▸ done

  b1 : Chain (CS24 ∷ Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (CS24 ∷ Sb0-1-23-4 ∷ [])
  b1 = at 1 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- auto BOX(0;1234) | CS02: 1 steps
lem-auto-BOX⟨0·1234⟩-∣-CS02 : Ws → ⟪ (Bx0-1234 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS02 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CS02 ∷ []) (CS02 ∷ Bx0-1234 ∷ [])
  b0 = at 0 2 (CS02 ∷ Bx0-1234 ∷ []) (sym (lem-CS20-beta-c c4)) ▸ done


-- auto SBOX(0;1;23;4) | CS02: 11 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS02 : Ws → ⟪ (Sb0-1-23-4 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS02 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-23-4 ∷ CS02 ∷ []) (Bx0-1234 ∷ Toff423 ∷ CS02 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 1 (CS14⁻ ∷ []) (refl) ▸
       at 4 2 (CS02 ∷ CS14⁻ ∷ []) (sym (wp0099 c4)) ▸
       at 5 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 3 2 (CS02 ∷ Toff423 ∷ []) (sym (wp0098 c4)) ▸
       at 2 1 (CS14 ∷ []) (refl) ▸
       at 2 2 (CS02 ∷ CS14 ∷ []) (sym (wp0100 c4)) ▸
       at 3 1 (Sb0-1-4-3 ∷ []) (refl) ▸ done

  b1 : Chain (Bx0-1234 ∷ Toff423 ∷ CS02 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (CS02 ∷ Sb0-1-23-4 ∷ [])
  b1 = at 1 2 (CS02 ∷ Toff423 ∷ []) (sym (wp0098 c4)) ▸
       at 0 2 (CS02 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS02 c4) ▸
       at 1 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- auto SBOX(0;1;23;4) | CS14: 9 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS14 : Ws → ⟪ (Sb0-1-23-4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS14 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-23-4 ∷ CS14 ∷ []) (CS14 ∷ Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 1 (CS14⁻ ∷ []) (refl) ▸
       at 4 2 (CS14 ∷ CS14⁻ ∷ []) (sym (wl0299 (lit c4))) ▸
       at 5 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 2 1 (CS14 ∷ []) (refl) ▸
       at 1 4 (CS14 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ []) (sym (wl0300 (lit c4))) ▸
       at 3 1 (Sb0-1-4-3 ∷ []) (refl) ▸
       at 0 2 (CS14 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14 c4) ▸ done

  b1 : Chain (CS14 ∷ Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (CS14 ∷ Sb0-1-23-4 ∷ [])
  b1 = at 1 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- auto SBOX(0;1;23;4) | CCZ023: 44 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ023 : Ws → ⟪ (Sb0-1-23-4 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ023 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (run b5)))))
  where
  b0 : Chain (Sb0-1-23-4 ∷ CCZ023 ∷ []) (CS03 ∷ Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ CX23 ∷ CS14⁻ ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ [])
  b0 = at 1 1 (CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ []) (wl0353 (lit c4)) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS03 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS20-at2332 c4) ▸
       at 1 1 (Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ []) (refl) ▸
       at 5 1 (CS14⁻ ∷ []) (refl) ▸
       at 5 2 (CX23 ∷ CS14⁻ ∷ []) (wl0354 (lit c4)) ▸
       at 6 1 (Sb⁻0-1-4-2 ∷ []) (refl) ▸
       at 6 1 (CS14⁻ ∷ []) (refl) ▸ done

  b1 : Chain (CS03 ∷ Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ CX23 ∷ CS14⁻ ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ []) (CS03 ∷ Bx0-1324 ∷ Toff423 ∷ CX23 ∷ CS14 ∷ CS03⁻ ∷ CX23 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS02 ∷ [])
  b1 = at 6 2 (CS03⁻ ∷ CS14⁻ ∷ []) (sym (wp0118 c4)) ▸
       at 7 1 (Sb⁻0-1-4-2 ∷ []) (refl) ▸
       at 7 1 (CS14⁻ ∷ []) (refl) ▸
       at 7 2 (CX23 ∷ CS14⁻ ∷ []) (wl0354 (lit c4)) ▸
       at 8 1 (Sb⁻0-1-4-2 ∷ []) (refl) ▸
       at 4 4 (CX23 ∷ CS03⁻ ∷ CX23 ∷ Toff423 ∷ []) (sym (wp0119 c4)) ▸
       at 3 1 (CS14 ∷ []) (refl) ▸
       at 3 2 (CX23 ∷ CS14 ∷ []) (wl0355 (lit c4)) ▸ done

  b2 : Chain (CS03 ∷ Bx0-1324 ∷ Toff423 ∷ CX23 ∷ CS14 ∷ CS03⁻ ∷ CX23 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS02 ∷ []) (CS03 ∷ Bx0-1324 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS02 ∷ [])
  b2 = at 4 1 (Sb0-1-4-2 ∷ []) (refl) ▸
       at 4 1 (CS14 ∷ []) (refl) ▸
       at 4 2 (CS03⁻ ∷ CS14 ∷ []) (sym (wp0120 c4)) ▸
       at 5 1 (Sb0-1-4-2 ∷ []) (refl) ▸
       at 5 1 (CS14 ∷ []) (refl) ▸
       at 5 2 (CX23 ∷ CS14 ∷ []) (wl0355 (lit c4)) ▸
       at 6 1 (Sb0-1-4-2 ∷ []) (refl) ▸
       at 2 4 (CX23 ∷ CS03⁻ ∷ CX23 ∷ Toff423 ∷ []) (sym (wp0119 c4)) ▸ done

  b3 : Chain (CS03 ∷ Bx0-1324 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS02 ∷ []) (CS03 ∷ CX23 ∷ CCZ124 ∷ CS03⁻ ∷ CX23 ∷ CX23 ∷ Bx0-1234 ∷ CX23 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS02 ∷ [])
  b3 = at 1 0 (CX23 ∷ CX23 ∷ []) (sym (wl0218 (lit c4))) ▸
       at 3 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸
       at 2 3 (Bx0-1234 ∷ CCZ124 ∷ []) (lem-CX23-beta c4) ▸
       at 2 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 2 2 (CCZ124 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at2332 c4) ▸
       at 3 2 (CS03⁻ ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd20-at2332 c4) ▸
       at 4 0 (CX23 ∷ CX23 ∷ []) (sym (wl0218 (lit c4))) ▸
       at 6 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸ done

  b4 : Chain (CS03 ∷ CX23 ∷ CCZ124 ∷ CS03⁻ ∷ CX23 ∷ CX23 ∷ Bx0-1234 ∷ CX23 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS02 ∷ []) (CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS02 ∷ [])
  b4 = at 5 3 (Bx0-1234 ∷ CCZ124 ∷ []) (lem-CX23-beta c4) ▸
       at 5 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 5 2 (CCZ124 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at2332 c4) ▸
       at 1 2 (CCZ124 ∷ CX23 ∷ []) (sym (wl0356 (lit c4))) ▸
       at 4 2 (CCZ124 ∷ CX23 ∷ []) (sym (wl0356 (lit c4))) ▸
       at 3 2 (CCZ124 ∷ CS03⁻ ∷ []) (lem-comm-CSd03-CCZ124 (lit c4)) ▸
       at 2 2 (CCZ124 ∷ CX23 ∷ []) (sym (wl0356 (lit c4))) ▸
       at 1 2 [] (wl0351 (lit c4)) ▸ done

  b5 : Chain (CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS02 ∷ []) (CCZ023 ∷ Sb0-1-23-4 ∷ [])
  b5 = at 4 5 (Sb0-1-32-4 ∷ []) (refl) ▸
       at 4 2 (CS02 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS30-at2332 c4) ▸
       at 5 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 5 (CCZ023 ∷ []) (sym (wl0353 (lit c4))) ▸ done


-- auto SBOX(0;1;23;4) | CCZ023 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ023-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ023-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 (CCZ023 ∷ Sw23 ∷ []) (sym (wl0065 (lit c4))) ▸
       at 1 2 (CCZ023 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ023 c4) ▸
       at 0 2 (CCZ023 ∷ Sw23 ∷ []) (sym (wl0065 (lit c4))) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(0;1432) @2332: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩-at2332 : Ws → ⟪ (Sb⁻0-1-3-2 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ Sb⁻0-1-3-2 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-3-2 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ Sb⁻0-1-3-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb⁻0-1-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·3·2⟩ (lit c4)) ▸
       at 2 2 (Bx0-1432 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1423⟩ (lit c4)) ▸
       at 1 2 (Bx0-1432 ∷ Sb⁻0-1-2-3 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩ c4) ▸
       at 0 2 (Bx0-1423 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1432⟩ (lit c4)) ▸
       at 1 2 (Sb⁻0-1-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·2·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(0;1432) @243243: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩-at243243 : Ws → ⟪ (Sb⁻0-1-4-2 ∷ Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ Sb⁻0-1-4-2 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-4-2 ∷ Bx0-1324 ∷ []) (Bx0-1324 ∷ Sb⁻0-1-4-2 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Sb⁻0-1-3-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·4·2⟩ (lit c4)) ▸
       at 2 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ (lit c4)) ▸
       at 1 2 (Bx0-1423 ∷ Sb⁻0-1-3-2 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩-at2332 c4) ▸
       at 0 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ (lit c4)) ▸
       at 1 2 (Sb⁻0-1-4-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·3·2⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(0;1432) @2442: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩-at2442 : Ws → ⟪ (Sb⁻0-1-4-3 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ Sb⁻0-1-4-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩-at2442 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-4-3 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb⁻0-1-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·4·3⟩ (lit c4)) ▸
       at 2 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ (lit c4)) ▸
       at 1 2 (Bx0-1324 ∷ Sb⁻0-1-4-2 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩-at243243 c4) ▸
       at 0 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ (lit c4)) ▸
       at 1 2 (Sb⁻0-1-4-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·4·2⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOX(0;1;2;3) | BOX(0;1432) @2332: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩-at2332 : Ws → ⟪ (Sb0-1-3-2 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ Sb0-1-3-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-3-2 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ Sb0-1-3-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·3·2⟩ (lit c4)) ▸
       at 2 2 (Bx0-1432 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1423⟩ (lit c4)) ▸
       at 1 2 (Bx0-1432 ∷ Sb0-1-2-3 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩ c4) ▸
       at 0 2 (Bx0-1423 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1432⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·2·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOX(0;1;2;3) | BOX(0;1432) @243243: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩-at243243 : Ws → ⟪ (Sb0-1-4-2 ∷ Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ Sb0-1-4-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-4-2 ∷ Bx0-1324 ∷ []) (Bx0-1324 ∷ Sb0-1-4-2 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Sb0-1-3-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·4·2⟩ (lit c4)) ▸
       at 2 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ (lit c4)) ▸
       at 1 2 (Bx0-1423 ∷ Sb0-1-3-2 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩-at2332 c4) ▸
       at 0 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-4-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·3·2⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto SBOX(0;1;2;3) | BOX(0;1432) @2442: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩-at2442 : Ws → ⟪ (Sb0-1-4-3 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ Sb0-1-4-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩-at2442 c4 = run b0
  where
  b0 : Chain (Sb0-1-4-3 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ Sb0-1-4-3 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·4·3⟩ (lit c4)) ▸
       at 2 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ (lit c4)) ▸
       at 1 2 (Bx0-1324 ∷ Sb0-1-4-2 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩-at243243 c4) ▸
       at 0 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-4-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·4·2⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | BOX(0;1234): 30 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·1234⟩ : Ws → ⟪ (Sb0-1-23-4 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·1234⟩ c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Sb0-1-23-4 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Bx0-2314 ∷ CCZ123 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 2 (Bx0-1234 ∷ Sb⁻0-1-4-3 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩-at2442 c4) ▸
       at 5 0 (Toff423 ∷ Toff423 ∷ []) (sym (wl0296 (lit c4))) ▸
       at 4 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 4 1 (Bx0-2314 ∷ []) (lem-sym23-at1221 c4) ▸
       at 4 1 (Bx0-2341 ∷ []) (lem-sym34-at122331 c4) ▸
       at 3 3 (Bx0-2341 ∷ CCZ123 ∷ []) (lem-T312-beta-at12233441 c4) ▸
       at 3 1 (Bx0-2314 ∷ []) (lem-sym34-at12233441 c4) ▸ done

  b1 : Chain (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Bx0-2314 ∷ CCZ123 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (Bx0-1234 ∷ Bx0-2341 ∷ CCZ123 ∷ Toff423 ∷ Sb0-1-4-3 ∷ CCZ123 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b1 = at 3 1 (Bx0-2134 ∷ []) (lem-sym23-at122331 c4) ▸
       at 3 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸
       at 2 2 (Bx0-1234 ∷ Sb0-1-4-3 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩-at2442 c4) ▸
       at 3 0 (Toff423 ∷ Toff423 ∷ []) (sym (wl0296 (lit c4))) ▸
       at 2 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 2 1 (Bx0-2314 ∷ []) (lem-sym23-at1221 c4) ▸
       at 2 1 (Bx0-2341 ∷ []) (lem-sym34-at122331 c4) ▸
       at 1 3 (Bx0-2341 ∷ CCZ123 ∷ []) (lem-T312-beta-at12233441 c4) ▸ done

  b2 : Chain (Bx0-1234 ∷ Bx0-2341 ∷ CCZ123 ∷ Toff423 ∷ Sb0-1-4-3 ∷ CCZ123 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (Bx0-1234 ∷ Bx0-1234 ∷ CCZ123 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ CCZ123 ∷ [])
  b2 = at 1 1 (Bx0-2314 ∷ []) (lem-sym34-at12233441 c4) ▸
       at 1 1 (Bx0-2134 ∷ []) (lem-sym23-at122331 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸
       at 0 2 (Bx0-1234 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨0·1234⟩ c4) ▸
       at 7 1 (CS14⁻ ∷ []) (refl) ▸
       at 5 3 (Toff423 ∷ CS14⁻ ∷ CCZ123 ∷ []) (wl0357 (lit c4)) ▸
       at 6 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 1 (CS14 ∷ []) (refl) ▸ done

  b3 : Chain (Bx0-1234 ∷ Bx0-1234 ∷ CCZ123 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ CCZ123 ∷ []) (Bx0-1234 ∷ Sb0-1-23-4 ∷ [])
  b3 = at 6 1 (CS14⁻ ∷ []) (refl) ▸
       at 2 5 (Toff423 ∷ CS14 ∷ Toff423 ∷ CS14⁻ ∷ CCZ123 ∷ []) (wl0358 (lit c4)) ▸
       at 3 1 (Sb0-1-4-3 ∷ []) (refl) ▸
       at 5 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 6 2 [] (wl0212 (lit c4)) ▸
       at 1 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- auto CCZ012 | SBOX(3;0;14;2): 9 steps
lem-auto-CCZ012-∣-SBOX⟨3·0·14·2⟩ : Ws → ⟪ (CCZ012 ∷ Sb3-0-14-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-14-2 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·0·14·2⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ012 ∷ Sb3-0-14-2 ∷ []) (Bx3-0142 ∷ Toff214 ∷ Sb3-0-2-4 ∷ Toff214 ∷ Sb⁻3-0-2-4 ∷ CCZ012 ∷ [])
  b0 = at 1 1 (Bx3-0142 ∷ Toff214 ∷ Sb3-0-2-4 ∷ Toff214 ∷ Sb⁻3-0-2-4 ∷ []) (refl) ▸
       at 0 2 (Bx3-0142 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0142⟩ c4) ▸
       at 3 1 (CS02 ∷ []) (refl) ▸
       at 1 4 (Toff214 ∷ CS02 ∷ Toff214 ∷ CCZ012 ∷ []) (wp0121 c4) ▸
       at 2 1 (Sb3-0-2-4 ∷ []) (refl) ▸
       at 5 1 (CS02⁻ ∷ []) (refl) ▸
       at 4 2 (CS02⁻ ∷ CCZ012 ∷ []) (wl0359 (lit c4)) ▸
       at 4 1 (Sb⁻3-0-2-4 ∷ []) (refl) ▸ done

  b1 : Chain (Bx3-0142 ∷ Toff214 ∷ Sb3-0-2-4 ∷ Toff214 ∷ Sb⁻3-0-2-4 ∷ CCZ012 ∷ []) (Sb3-0-14-2 ∷ CCZ012 ∷ [])
  b1 = at 0 5 (Sb3-0-14-2 ∷ []) (refl) ▸ done


-- auto SBOX(0;1;23;4) | CS14 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS14-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS14-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CS14 ∷ []) (CS14 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 (CS14 ∷ Sw23 ∷ []) (sym (wl0021 (lit c4))) ▸
       at 1 2 (CS14 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS14 c4) ▸
       at 0 2 (CS14 ∷ Sw23 ∷ []) (sym (wl0021 (lit c4))) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | SBOX(0;1;4;3): 5 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩ : Ws → ⟪ (Sb0-1-23-4 ∷ Sb0-1-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-4-3 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩ c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ Sb0-1-4-3 ∷ []) (Sb0-1-4-3 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 1 1 (CS14 ∷ []) (refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS14 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS14-at2332 c4) ▸
       at 1 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 1 (Sb0-1-4-3 ∷ []) (refl) ▸ done


-- auto SBOX(0;1;23;4) | CSd14: 9 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd14 : Ws → ⟪ (Sb0-1-23-4 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd14 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-23-4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 1 (CS14⁻ ∷ []) (refl) ▸
       at 4 2 (CS14⁻ ∷ CS14⁻ ∷ []) (wl0317 (lit c4)) ▸
       at 5 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 2 1 (CS14 ∷ []) (refl) ▸
       at 1 4 (CS14⁻ ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ []) (sym (wl0318 (lit c4))) ▸
       at 3 1 (Sb0-1-4-3 ∷ []) (refl) ▸
       at 0 2 (CS14⁻ ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14 c4) ▸ done

  b1 : Chain (CS14⁻ ∷ Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (CS14⁻ ∷ Sb0-1-23-4 ∷ [])
  b1 = at 1 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- auto SBOX(0;1;23;4) | CSd14 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd14-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd14-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 (CS14⁻ ∷ Sw23 ∷ []) (sym (wl0033 (lit c4))) ▸
       at 1 2 (CS14⁻ ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd14 c4) ▸
       at 0 2 (CS14⁻ ∷ Sw23 ∷ []) (sym (wl0033 (lit c4))) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | SBOXd(0;1;4;3): 5 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩ : Ws → ⟪ (Sb0-1-23-4 ∷ Sb⁻0-1-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-4-3 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩ c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ Sb⁻0-1-4-3 ∷ []) (Sb⁻0-1-4-3 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 1 1 (CS14⁻ ∷ []) (refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS14⁻ ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd14-at2332 c4) ▸
       at 1 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸ done


-- sym12 @01132032: 5 steps
lem-sym12-at01132032 : Ws → ⟪ (Bx1-3024 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0324 ∷ []) ⟫ʷ
lem-sym12-at01132032 c4 = run b0
  where
  b0 : Chain (Bx1-3024 ∷ []) (Bx1-0324 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-3124 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·3024⟩ (lit c4)) ▸
       at 1 1 (Bx0-1324 ∷ []) (lem-sym12-at132132 c4) ▸
       at 0 2 (Bx1-0324 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1324⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- sym12 @02132031: 5 steps
lem-sym12-at02132031 : Ws → ⟪ (Bx2-3014 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0314 ∷ []) ⟫ʷ
lem-sym12-at02132031 c4 = run b0
  where
  b0 : Chain (Bx2-3014 ∷ []) (Bx2-0314 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx1-3024 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·3014⟩ (lit c4)) ▸
       at 1 1 (Bx1-0324 ∷ []) (lem-sym12-at01132032 c4) ▸
       at 0 2 (Bx2-0314 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0324⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- sym12 @02132130: 5 steps
lem-sym12-at02132130 : Ws → ⟪ (Bx2-3104 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1304 ∷ []) ⟫ʷ
lem-sym12-at02132130 c4 = run b0
  where
  b0 : Chain (Bx2-3104 ∷ []) (Bx2-1304 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx2-3014 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·3104⟩ (lit c4)) ▸
       at 1 1 (Bx2-0314 ∷ []) (lem-sym12-at02132031 c4) ▸
       at 0 2 (Bx2-1304 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·0314⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- sym23 @022330: 5 steps
lem-sym23-at022330 : Ws → ⟪ (Bx2-1304 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1034 ∷ []) ⟫ʷ
lem-sym23-at022330 c4 = run b0
  where
  b0 : Chain (Bx2-1304 ∷ []) (Bx2-1034 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx2-0314 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1304⟩ (lit c4)) ▸
       at 1 1 (Bx2-0134 ∷ []) (lem-sym23-at02102331 c4) ▸
       at 0 2 (Bx2-1034 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·0134⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- CSd12-beta @0110: 7 steps
lem-CSd12-beta-at0110 : Ws → ⟪ (CS02⁻ ∷ Bx1-0234 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0234 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-CSd12-beta-at0110 c4 = run b0
  where
  b0 : Chain (CS02⁻ ∷ Bx1-0234 ∷ []) (Bx1-0234 ∷ CS02⁻ ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CS12⁻ ∷ Sw01 ∷ []) (sym (wl0139 (lit c4))) ▸
       at 2 2 (Bx0-1234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0234⟩ (lit c4)) ▸
       at 1 2 (Bx0-1234 ∷ CS12⁻ ∷ []) (lem-CSd12-beta c4) ▸
       at 0 2 (Bx1-0234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1234⟩ (lit c4)) ▸
       at 1 2 (CS02⁻ ∷ Sw01 ∷ []) (sym (wl0036 (lit c4))) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- CSd12-beta @021021: 7 steps
lem-CSd12-beta-at021021 : Ws → ⟪ (CS01⁻ ∷ Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ CS01⁻ ∷ []) ⟫ʷ
lem-CSd12-beta-at021021 c4 = run b0
  where
  b0 : Chain (CS01⁻ ∷ Bx2-0134 ∷ []) (Bx2-0134 ∷ CS01⁻ ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CS02⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd01 (lit c4)) ▸
       at 2 2 (Bx1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0134⟩ (lit c4)) ▸
       at 1 2 (Bx1-0234 ∷ CS02⁻ ∷ []) (lem-CSd12-beta-at0110 c4) ▸
       at 0 2 (Bx2-0134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0234⟩ (lit c4)) ▸
       at 1 2 (CS01⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd02 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- CSd12-beta @0220: 7 steps
lem-CSd12-beta-at0220 : Ws → ⟪ (CS01⁻ ∷ Bx2-1034 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1034 ∷ CS01⁻ ∷ []) ⟫ʷ
lem-CSd12-beta-at0220 c4 = run b0
  where
  b0 : Chain (CS01⁻ ∷ Bx2-1034 ∷ []) (Bx2-1034 ∷ CS01⁻ ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CS01⁻ ∷ Sw01 ∷ []) (sym (wl0133 (lit c4))) ▸
       at 2 2 (Bx2-0134 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1034⟩ (lit c4)) ▸
       at 1 2 (Bx2-0134 ∷ CS01⁻ ∷ []) (lem-CSd12-beta-at021021 c4) ▸
       at 0 2 (Bx2-1034 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·0134⟩ (lit c4)) ▸
       at 1 2 (CS01⁻ ∷ Sw01 ∷ []) (sym (wl0133 (lit c4))) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- sym23 @0220: 5 steps
lem-sym23-at0220 : Ws → ⟪ (Bx2-1034 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1304 ∷ []) ⟫ʷ
lem-sym23-at0220 c4 = run b0
  where
  b0 : Chain (Bx2-1034 ∷ []) (Bx2-1304 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx2-0134 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1034⟩ (lit c4)) ▸
       at 1 1 (Bx2-0314 ∷ []) (lem-sym23-at021021 c4) ▸
       at 0 2 (Bx2-1304 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·0314⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- sym12 @01102332: 5 steps
lem-sym12-at01102332 : Ws → ⟪ (Bx1-0324 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3024 ∷ []) ⟫ʷ
lem-sym12-at01102332 c4 = run b0
  where
  b0 : Chain (Bx1-0324 ∷ []) (Bx1-3024 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-1324 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0324⟩ (lit c4)) ▸
       at 1 1 (Bx0-3124 ∷ []) (lem-sym12-at2332 c4) ▸
       at 0 2 (Bx1-3024 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·3124⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- sym12 @02102331: 5 steps
lem-sym12-at02102331 : Ws → ⟪ (Bx2-0314 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3014 ∷ []) ⟫ʷ
lem-sym12-at02102331 c4 = run b0
  where
  b0 : Chain (Bx2-0314 ∷ []) (Bx2-3014 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx1-0324 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0314⟩ (lit c4)) ▸
       at 1 1 (Bx1-3024 ∷ []) (lem-sym12-at01102332 c4) ▸
       at 0 2 (Bx2-3014 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·3024⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- sym12 @022330: 5 steps
lem-sym12-at022330 : Ws → ⟪ (Bx2-1304 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3104 ∷ []) ⟫ʷ
lem-sym12-at022330 c4 = run b0
  where
  b0 : Chain (Bx2-1304 ∷ []) (Bx2-3104 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx2-0314 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1304⟩ (lit c4)) ▸
       at 1 1 (Bx2-3014 ∷ []) (lem-sym12-at02102331 c4) ▸
       at 0 2 (Bx2-3104 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·3014⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- auto CSd01 | BOX(2;3104): 7 steps
lem-auto-CSd01-∣-BOX⟨2·3104⟩ : Ws → ⟪ (CS01⁻ ∷ Bx2-3104 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3104 ∷ CS01⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨2·3104⟩ c4 = run b0
  where
  b0 : Chain (CS01⁻ ∷ Bx2-3104 ∷ []) (Bx2-3104 ∷ CS01⁻ ∷ [])
  b0 = at 0 1 (CS01⁻ ∷ []) (wl0360 (lit c4)) ▸
       at 1 1 (Bx2-1304 ∷ []) (lem-sym12-at02132130 c4) ▸
       at 1 1 (Bx2-1034 ∷ []) (lem-sym23-at022330 c4) ▸
       at 0 2 (Bx2-1034 ∷ CS01⁻ ∷ []) (lem-CSd12-beta-at0220 c4) ▸
       at 0 1 (Bx2-1304 ∷ []) (lem-sym23-at0220 c4) ▸
       at 0 1 (Bx2-3104 ∷ []) (lem-sym12-at022330 c4) ▸
       at 1 1 (CS01⁻ ∷ []) (wl0360 (lit c4)) ▸ done


-- beta-T @01122330: 8 steps
lem-beta-T-at01122330 : Ws → ⟪ (Bx1-2304 ∷ []) ⟫ʷ ≈ ⟪ (Toff123 ∷ CCZ014 ∷ Toff123 ∷ CCZ014 ∷ []) ⟫ʷ
lem-beta-T-at01122330 c4 = run b0
  where
  b0 : Chain (Bx1-2304 ∷ []) (Toff123 ∷ CCZ014 ∷ Toff123 ∷ CCZ014 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-2314 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2304⟩ (lit c4)) ▸
       at 1 1 (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) (lem-beta-T-at122331 c4) ▸
       at 0 2 (Toff123 ∷ Sw01 ∷ []) (wl0108 (lit c4)) ▸
       at 1 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 (lit c4)) ▸
       at 2 2 (Toff123 ∷ Sw01 ∷ []) (wl0108 (lit c4)) ▸
       at 3 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 (lit c4)) ▸
       at 4 2 [] (wl0002 (lit c4)) ▸ done


-- auto S0 | BOX(1;2304): 6 steps
lem-auto-S0-∣-BOX⟨1·2304⟩ : Ws → ⟪ (S0 ∷ Bx1-2304 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2304 ∷ S0 ∷ []) ⟫ʷ
lem-auto-S0-∣-BOX⟨1·2304⟩ c4 = run b0
  where
  b0 : Chain (S0 ∷ Bx1-2304 ∷ []) (Bx1-2304 ∷ S0 ∷ [])
  b0 = at 1 1 (Toff123 ∷ CCZ014 ∷ Toff123 ∷ CCZ014 ∷ []) (lem-beta-T-at01122330 c4) ▸
       at 0 2 (Toff123 ∷ S0 ∷ []) (c₁ (S) (Toff)) ▸
       at 1 2 (CCZ014 ∷ S0 ∷ []) (sym (wp0122 c4)) ▸
       at 2 2 (Toff123 ∷ S0 ∷ []) (c₁ (S) (Toff)) ▸
       at 3 2 (CCZ014 ∷ S0 ∷ []) (sym (wp0122 c4)) ▸
       at 0 4 (Bx1-2304 ∷ []) (sym (lem-beta-T-at01122330 c4)) ▸ done


{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D137 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)
open import Examples.Groups.Clifford+CS.Five.Resps using (pw0 ; pw1 ; pw2 ; pw3 ; pw4)
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-CX23-beta ; lem-T-beta ; lem-sym12 ; lem-sym23 ; lem-sym34)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-c124-beta-at3443 ; lem-sym12-at1221 ; lem-sym12-at132132 ; lem-sym23-at1221 ; lem-sym23-at132132 ; lem-sym34-at1221)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-Cz-beta-at12243143 ; lem-Cz-beta-at13243142 ; lem-Cz-beta-at243243 ; lem-sym12-at233442 ; lem-sym23-at011220 ; lem-sym23-at01122330 ; lem-sym23-at12213443 ; lem-sym23-at122331 ; lem-sym23-at12243143 ; lem-sym23-at13213442 ; lem-sym23-at13243142 ; lem-sym23-at2332 ; lem-sym23-at243243 ; lem-sym23-at3443 ; lem-sym34-at12213443 ; lem-sym34-at13213442 ; lem-sym34-at2332 ; lem-sym34-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-sym12-at2332 ; lem-sym34-at122331 ; lem-sym34-at12233441 ; lem-sym34-at233442)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-auto-BOX⟨0·1234⟩-∣-CSd14-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at2332 ; lem-sym12-at13213442)
open import Examples.Groups.Clifford+CS.Five.D.D007 using (lem-SBsym-at0113203442 ; lem-T312-beta-at233442 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CS24-at2332 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at2332 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd4-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D009 using (lem-CX23-beta-at1221 ; lem-CX23-beta-at132132 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ214-at2332 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ314-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D010 using (lem-CS20-beta-ci-at011220 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CS14-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D011 using (lem-CS20-beta-c-at011220)
open import Examples.Groups.Clifford+CS.Five.D.D079 using (lem-CSd12-beta-at12243143 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CS34-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D080 using (lem-auto-BOX⟨0·1234⟩-∣-CSd34-at2332 ; lem-sym23-at1331)
open import Examples.Groups.Clifford+CS.Five.D.D135 using (lem-sym12-at0410233142)
open import Examples.Groups.Clifford+CS.Five.D.D136 using (lem-CX23-beta-at1331 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ234-at2332 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ431 ; lem-beta-T-at0410213243 ; lem-sym12-at0413203142 ; lem-sym23-at0413203142 ; lem-sym23-at0413213042)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-BOX⟨0·2134⟩ ; lem-nat-1-CCZ024 ; lem-nat-2-BOX⟨0·1234⟩ ; lem-nat-2-BOX⟨0·1324⟩ ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ013 ; lem-nat-2-TOFF301 ; lem-nat-3-CCZ014)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-1-CCZ014 ; lem-nat-2-TOFF201 ; lem-nat-3-CCZ013)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-CCZ124 ; lem-nat-2-CCZ124 ; lem-nat-2-CCZ134)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-0-TOFF403)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-1-BOX⟨0·1234⟩)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-0-TOFF401 ; lem-nat-0-TOFF413 ; lem-nat-1-TOFF401 ; lem-nat-2-TOFF402 ; lem-nat-3-TOFF301)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-2-BOX⟨2·0314⟩ ; lem-nat-2-BOX⟨3·0214⟩ ; lem-nat-3-CCZ123 ; lem-nat-3-CCZ124)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-nat-1-BOX⟨0·1342⟩ ; lem-nat-1-BOX⟨0·2341⟩ ; lem-nat-1-CS01 ; lem-nat-1-CS02)
open import Examples.Groups.Clifford+CS.Five.D.R013 using (lem-nat-2-TOFF403)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-1-CSd02 ; lem-nat-2-SBOX⟨0·1·23·4⟩ ; lem-nat-2-SBOX⟨0·1·32·4⟩ ; lem-nat-2-SBOXd⟨0·1·4·2⟩ ; lem-nat-2-SBOXd⟨0·1·4·3⟩ ; lem-nat-3-SBOX⟨0·1·3·2⟩ ; lem-nat-3-SBOX⟨0·1·4·2⟩ ; lem-nat-3-SBOXd⟨0·1·3·2⟩ ; lem-nat-3-SBOXd⟨0·1·4·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-1-CSd01)
open import Examples.Groups.Clifford+CS.Five.D.R016 using (lem-nat-1-BOX⟨4·0312⟩)
open import Examples.Groups.Clifford+CS.Five.D.R017 using (lem-nat-1-TOFF402 ; lem-nat-3-TOFF401)
open import Examples.Groups.Clifford+CS.Five.D.R019 using (lem-nat-0-BOX⟨2·0314⟩ ; lem-nat-0-BOX⟨2·1304⟩ ; lem-nat-2-SBOX⟨0·1·2·3⟩ ; lem-nat-2-SBOX⟨0·1·3·2⟩ ; lem-nat-2-SBOXd⟨0·1·2·3⟩ ; lem-nat-2-SBOXd⟨0·1·3·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R021 using (lem-nat-1-BOX⟨1·3240⟩ ; lem-nat-1-BOX⟨2·3140⟩)
open import Examples.Groups.Clifford+CS.Five.D.R029 using (lem-nat-0-BOX⟨4·0321⟩ ; lem-nat-0-BOX⟨4·1320⟩ ; lem-nat-1-BOX⟨4·0321⟩ ; lem-nat-2-BOX⟨4·0312⟩ ; lem-nat-3-BOX⟨3·0214⟩)
open import Examples.Groups.Clifford+CS.Five.D.R030 using (lem-nat-0-BOX⟨4·1023⟩ ; lem-nat-0-BOX⟨4·3102⟩ ; lem-nat-1-BOX⟨4·2013⟩ ; lem-nat-2-BOX⟨4·0213⟩ ; lem-nat-2-BOX⟨4·3012⟩)
open import Examples.Groups.Clifford+CS.Five.D.R031 using (lem-nat-0-BOX⟨0·3241⟩ ; lem-nat-0-BOX⟨1·3240⟩ ; lem-nat-1-BOX⟨0·3142⟩ ; lem-nat-1-BOX⟨0·3241⟩ ; lem-nat-1-BOX⟨1·2304⟩ ; lem-nat-1-BOX⟨2·1304⟩ ; lem-nat-1-BOX⟨4·1230⟩ ; lem-nat-1-BOX⟨4·2130⟩ ; lem-nat-2-BOX⟨2·3140⟩ ; lem-nat-2-BOX⟨3·2140⟩ ; lem-nat-2-BOX⟨4·1230⟩ ; lem-nat-2-BOX⟨4·1320⟩ ; lem-nat-3-BOX⟨3·2140⟩ ; lem-nat-3-BOX⟨4·0213⟩ ; lem-nat-3-BOX⟨4·2130⟩)
-- auto SBOX(0;1;23;4) | CCZ431 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ431-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ431-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 1 2 (CCZ134 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ431 c4) ▸
       at 0 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | TOFF421: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF421 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF421 c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ Toff412 ∷ []) (Toff412 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 1 1 (K4 ∷ CCZ124 ∷ K4⁻ ∷ []) (lw0 c4 (Toff412 ∷ []) (K4 ∷ CCZ124 ∷ K4⁻ ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (K4 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at2332 c4) ▸
       at 1 2 (CCZ124 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ431-at2332 c4) ▸
       at 2 2 (K4⁻ ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd4-at2332 c4) ▸
       at 3 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 3 (Toff412 ∷ []) (lw0 c4 (K4 ∷ CCZ124 ∷ K4⁻ ∷ []) (Toff412 ∷ []) tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CCZ421: 32 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ421 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ421 c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Sb0-1-23-4 ∷ CCZ124 ∷ []) (CS14 ∷ Bx0-1324 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ CX21 ∷ CS14⁻ ∷ CX21 ∷ Sb⁻0-1-4-2 ∷ CS24 ∷ [])
  b0 = at 1 1 (CS14 ∷ CX21 ∷ CS14⁻ ∷ CX21 ∷ CS24 ∷ []) (lw0 c4 (CCZ124 ∷ []) (CS14 ∷ CX21 ∷ CS14⁻ ∷ CX21 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS14 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS14-at2332 c4) ▸
       at 1 1 (Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ []) (refl) ▸
       at 5 1 (CS14⁻ ∷ []) (refl) ▸
       at 5 4 (CX21 ∷ CS14⁻ ∷ CX21 ∷ CS14⁻ ∷ []) (lw0 c4 (CS14⁻ ∷ CX21 ∷ CS14⁻ ∷ CX21 ∷ []) (CX21 ∷ CS14⁻ ∷ CX21 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 8 1 (Sb⁻0-1-4-2 ∷ []) (refl) ▸
       at 3 1 (CS14 ∷ []) (refl) ▸ done

  b1 : Chain (CS14 ∷ Bx0-1324 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ CX21 ∷ CS14⁻ ∷ CX21 ∷ Sb⁻0-1-4-2 ∷ CS24 ∷ []) (CS14 ∷ CX21 ∷ Bx0-1324 ∷ CCZ234 ∷ CS14⁻ ∷ CX21 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS24 ∷ [])
  b1 = at 2 6 (CX21 ∷ CS14⁻ ∷ CX21 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ []) (lw0 c4 (Toff423 ∷ CS14 ∷ Toff423 ∷ CX21 ∷ CS14⁻ ∷ CX21 ∷ []) (CX21 ∷ CS14⁻ ∷ CX21 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sb0-1-4-2 ∷ []) (refl) ▸
       at 1 0 (CX21 ∷ CX21 ∷ []) (lw4 c4 [] (CX21 ∷ CX21 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Bx0-3124 ∷ []) (lem-sym12-at2332 c4) ▸
       at 3 1 (Bx0-3214 ∷ []) (lem-sym23-at132132 c4) ▸
       at 2 3 (Bx0-3214 ∷ CCZ234 ∷ []) (lem-CX23-beta-at1331 c4) ▸
       at 2 1 (Bx0-3124 ∷ []) (lem-sym23-at1331 c4) ▸
       at 2 1 (Bx0-1324 ∷ []) (lem-sym12-at132132 c4) ▸ done

  b2 : Chain (CS14 ∷ CX21 ∷ Bx0-1324 ∷ CCZ234 ∷ CS14⁻ ∷ CX21 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS24 ∷ []) (CS14 ∷ CX21 ∷ CCZ234 ∷ CS14⁻ ∷ CX21 ∷ Bx0-1324 ∷ CCZ234 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS24 ∷ [])
  b2 = at 2 2 (CCZ234 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ234-at2332 c4) ▸
       at 3 2 (CS14⁻ ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14-at2332 c4) ▸
       at 4 0 (CX21 ∷ CX21 ∷ []) (lw4 c4 [] (CX21 ∷ CX21 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Bx0-3124 ∷ []) (lem-sym12-at2332 c4) ▸
       at 6 1 (Bx0-3214 ∷ []) (lem-sym23-at132132 c4) ▸
       at 5 3 (Bx0-3214 ∷ CCZ234 ∷ []) (lem-CX23-beta-at1331 c4) ▸
       at 5 1 (Bx0-3124 ∷ []) (lem-sym23-at1331 c4) ▸
       at 5 1 (Bx0-1324 ∷ []) (lem-sym12-at132132 c4) ▸ done

  b3 : Chain (CS14 ∷ CX21 ∷ CCZ234 ∷ CS14⁻ ∷ CX21 ∷ Bx0-1324 ∷ CCZ234 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS24 ∷ []) (CCZ124 ∷ Sb0-1-23-4 ∷ [])
  b3 = at 5 2 (CCZ234 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ234-at2332 c4) ▸
       at 1 2 (CCZ234 ∷ CX21 ∷ []) (lw0 c4 (CX21 ∷ CCZ234 ∷ []) (CCZ234 ∷ CX21 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (CCZ234 ∷ CX21 ∷ CS14⁻ ∷ CX21 ∷ []) (lw0 c4 (CX21 ∷ CS14⁻ ∷ CX21 ∷ CCZ234 ∷ []) (CCZ234 ∷ CX21 ∷ CS14⁻ ∷ CX21 ∷ []) tt tt Eq.refl) ▸
       at 1 2 [] (lw0 c4 (CCZ234 ∷ CCZ234 ∷ []) [] tt tt Eq.refl) ▸
       at 4 5 (Sb0-1-32-4 ∷ []) (refl) ▸
       at 4 2 (CS24 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS34-at2332 c4) ▸
       at 5 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 5 (CCZ124 ∷ []) (lw0 c4 (CS14 ∷ CX21 ∷ CS14⁻ ∷ CX21 ∷ CS24 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CSd24: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd24 : Complete 4 → ⟪ (Bx0-1234 ∷ CS24⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS24⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ
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


-- auto BOX(0;1234) | CSd24 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd24-at2332 : Complete 4 → ⟪ (Bx0-1324 ∷ CS34⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS34⁻ ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd24-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ c4) ▸
       at 2 2 (CS24⁻ ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS34⁻ ∷ []) (CS24⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS24⁻ ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd24 c4) ▸
       at 0 2 (CS34⁻ ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS24⁻ ∷ []) (CS34⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CCZ423: 30 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ423 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ423 c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Sb0-1-23-4 ∷ CCZ234 ∷ []) (CS34 ∷ Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS24 ∷ [])
  b0 = at 1 1 (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) (lw0 c4 (CCZ234 ∷ []) (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS34 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS24-at2332 c4) ▸
       at 1 1 (Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ []) (refl) ▸
       at 5 1 (CS14⁻ ∷ []) (refl) ▸
       at 5 4 (CX23 ∷ CS34⁻ ∷ CX23 ∷ CS14⁻ ∷ []) (lw0 c4 (CS14⁻ ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ []) (CX23 ∷ CS34⁻ ∷ CX23 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 8 1 (Sb⁻0-1-4-2 ∷ []) (refl) ▸
       at 4 4 (CX23 ∷ CS34⁻ ∷ CX23 ∷ Toff423 ∷ []) (lw0 c4 (Toff423 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ []) (CX23 ∷ CS34⁻ ∷ CX23 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CS34 ∷ Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS24 ∷ []) (CS34 ∷ CX23 ∷ Bx0-1324 ∷ CCZ124 ∷ CS34⁻ ∷ CX23 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS24 ∷ [])
  b1 = at 3 1 (CS14 ∷ []) (refl) ▸
       at 3 4 (CX23 ∷ CS34⁻ ∷ CX23 ∷ CS14 ∷ []) (lw0 c4 (CS14 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ []) (CX23 ∷ CS34⁻ ∷ CX23 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sb0-1-4-2 ∷ []) (refl) ▸
       at 2 4 (CX23 ∷ CS34⁻ ∷ CX23 ∷ Toff423 ∷ []) (lw0 c4 (Toff423 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ []) (CX23 ∷ CS34⁻ ∷ CX23 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 1 0 (CX23 ∷ CX23 ∷ []) (lw4 c4 [] (CX23 ∷ CX23 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸
       at 2 3 (Bx0-1234 ∷ CCZ124 ∷ []) (lem-CX23-beta c4) ▸
       at 2 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸ done

  b2 : Chain (CS34 ∷ CX23 ∷ Bx0-1324 ∷ CCZ124 ∷ CS34⁻ ∷ CX23 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS24 ∷ []) (CS34 ∷ CCZ124 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CCZ124 ∷ Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS24 ∷ [])
  b2 = at 2 2 (CCZ124 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at2332 c4) ▸
       at 3 2 (CS34⁻ ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd24-at2332 c4) ▸
       at 4 0 (CX23 ∷ CX23 ∷ []) (lw4 c4 [] (CX23 ∷ CX23 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸
       at 5 3 (Bx0-1234 ∷ CCZ124 ∷ []) (lem-CX23-beta c4) ▸
       at 5 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 5 2 (CCZ124 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at2332 c4) ▸
       at 1 2 (CCZ124 ∷ CX23 ∷ []) (lw0 c4 (CX23 ∷ CCZ124 ∷ []) (CCZ124 ∷ CX23 ∷ []) tt tt Eq.refl) ▸ done

  b3 : Chain (CS34 ∷ CCZ124 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CCZ124 ∷ Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS24 ∷ []) (CCZ234 ∷ Sb0-1-23-4 ∷ [])
  b3 = at 2 4 (CCZ124 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ []) (lw0 c4 (CX23 ∷ CS34⁻ ∷ CX23 ∷ CCZ124 ∷ []) (CCZ124 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 [] (lw0 c4 (CCZ124 ∷ CCZ124 ∷ []) [] tt tt Eq.refl) ▸
       at 4 5 (Sb0-1-32-4 ∷ []) (refl) ▸
       at 4 2 (CS24 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS34-at2332 c4) ▸
       at 5 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 5 (CCZ234 ∷ []) (lw0 c4 (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CCZ412: 28 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ412 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ412 c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Sb0-1-23-4 ∷ CCZ124 ∷ []) (CS24 ∷ Bx0-1324 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ Sb⁻0-1-4-2 ∷ CS14 ∷ [])
  b0 = at 1 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (lw0 c4 (CCZ124 ∷ []) (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS24 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS34-at2332 c4) ▸
       at 1 1 (Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ []) (refl) ▸
       at 5 1 (CS14⁻ ∷ []) (refl) ▸
       at 5 4 (CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14⁻ ∷ []) (lw0 c4 (CS14⁻ ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ []) (CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 8 1 (Sb⁻0-1-4-2 ∷ []) (refl) ▸
       at 3 1 (CS14 ∷ []) (refl) ▸ done

  b1 : Chain (CS24 ∷ Bx0-1324 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ Sb⁻0-1-4-2 ∷ CS14 ∷ []) (CS24 ∷ CX12 ∷ CCZ134 ∷ CS24⁻ ∷ Bx0-1324 ∷ CX12 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS14 ∷ [])
  b1 = at 2 6 (CX12 ∷ CS24⁻ ∷ CX12 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ []) (lw0 c4 (Toff423 ∷ CS14 ∷ Toff423 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ []) (CX12 ∷ CS24⁻ ∷ CX12 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sb0-1-4-2 ∷ []) (refl) ▸
       at 1 0 (CX12 ∷ CX12 ∷ []) (lw4 c4 [] (CX12 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Bx0-3124 ∷ []) (lem-sym12-at2332 c4) ▸
       at 2 3 (Bx0-3124 ∷ CCZ134 ∷ []) (lem-CX23-beta-at132132 c4) ▸
       at 2 1 (Bx0-1324 ∷ []) (lem-sym12-at132132 c4) ▸
       at 2 2 (CCZ134 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ214-at2332 c4) ▸
       at 3 2 (CS24⁻ ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd34-at2332 c4) ▸ done

  b2 : Chain (CS24 ∷ CX12 ∷ CCZ134 ∷ CS24⁻ ∷ Bx0-1324 ∷ CX12 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS14 ∷ []) (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS14 ∷ [])
  b2 = at 4 0 (CX12 ∷ CX12 ∷ []) (lw4 c4 [] (CX12 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Bx0-3124 ∷ []) (lem-sym12-at2332 c4) ▸
       at 5 3 (Bx0-3124 ∷ CCZ134 ∷ []) (lem-CX23-beta-at132132 c4) ▸
       at 5 1 (Bx0-1324 ∷ []) (lem-sym12-at132132 c4) ▸
       at 5 2 (CCZ134 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ214-at2332 c4) ▸
       at 1 2 (CCZ134 ∷ CX12 ∷ []) (lw0 c4 (CX12 ∷ CCZ134 ∷ []) (CCZ134 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (CCZ134 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ []) (lw0 c4 (CX12 ∷ CS24⁻ ∷ CX12 ∷ CCZ134 ∷ []) (CCZ134 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 [] (lw0 c4 (CCZ134 ∷ CCZ134 ∷ []) [] tt tt Eq.refl) ▸ done

  b3 : Chain (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS14 ∷ []) (CCZ124 ∷ Sb0-1-23-4 ∷ [])
  b3 = at 4 5 (Sb0-1-32-4 ∷ []) (refl) ▸
       at 4 2 (CS14 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS14-at2332 c4) ▸
       at 5 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 5 (CCZ124 ∷ []) (lw0 c4 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CCZ412 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ412-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ412-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CCZ134 ∷ []) (CCZ134 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 1 2 (CCZ124 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ412 c4) ▸
       at 0 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | TOFF413: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF413 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF413 c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ Toff413 ∷ []) (Toff413 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 1 1 (K4 ∷ CCZ134 ∷ K4⁻ ∷ []) (lw0 c4 (Toff413 ∷ []) (K4 ∷ CCZ134 ∷ K4⁻ ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (K4 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at2332 c4) ▸
       at 1 2 (CCZ134 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ412-at2332 c4) ▸
       at 2 2 (K4⁻ ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd4-at2332 c4) ▸
       at 3 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 3 (Toff413 ∷ []) (lw0 c4 (K4 ∷ CCZ134 ∷ K4⁻ ∷ []) (Toff413 ∷ []) tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CCZ413: 32 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ413 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ413 c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Sb0-1-23-4 ∷ CCZ134 ∷ []) (CS34 ∷ Bx0-1324 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ Sb⁻0-1-4-2 ∷ CS14 ∷ [])
  b0 = at 1 1 (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) (lw0 c4 (CCZ134 ∷ []) (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS34 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS24-at2332 c4) ▸
       at 1 1 (Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ []) (refl) ▸
       at 5 1 (CS14⁻ ∷ []) (refl) ▸
       at 5 4 (CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14⁻ ∷ []) (lw0 c4 (CS14⁻ ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ []) (CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 8 1 (Sb⁻0-1-4-2 ∷ []) (refl) ▸
       at 3 1 (CS14 ∷ []) (refl) ▸ done

  b1 : Chain (CS34 ∷ Bx0-1324 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ Sb⁻0-1-4-2 ∷ CS14 ∷ []) (CS34 ∷ CX13 ∷ Bx0-1324 ∷ CCZ124 ∷ CS34⁻ ∷ CX13 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS14 ∷ [])
  b1 = at 2 6 (CX13 ∷ CS34⁻ ∷ CX13 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ []) (lw0 c4 (Toff423 ∷ CS14 ∷ Toff423 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ []) (CX13 ∷ CS34⁻ ∷ CX13 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sb0-1-4-2 ∷ []) (refl) ▸
       at 1 0 (CX13 ∷ CX13 ∷ []) (lw4 c4 [] (CX13 ∷ CX13 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸
       at 3 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 2 3 (Bx0-2134 ∷ CCZ124 ∷ []) (lem-CX23-beta-at1221 c4) ▸
       at 2 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸
       at 2 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸ done

  b2 : Chain (CS34 ∷ CX13 ∷ Bx0-1324 ∷ CCZ124 ∷ CS34⁻ ∷ CX13 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS14 ∷ []) (CS34 ∷ CX13 ∷ CCZ124 ∷ CS34⁻ ∷ CX13 ∷ Bx0-1324 ∷ CCZ124 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS14 ∷ [])
  b2 = at 2 2 (CCZ124 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ314-at2332 c4) ▸
       at 3 2 (CS34⁻ ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd24-at2332 c4) ▸
       at 4 0 (CX13 ∷ CX13 ∷ []) (lw4 c4 [] (CX13 ∷ CX13 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸
       at 6 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 5 3 (Bx0-2134 ∷ CCZ124 ∷ []) (lem-CX23-beta-at1221 c4) ▸
       at 5 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸
       at 5 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸ done

  b3 : Chain (CS34 ∷ CX13 ∷ CCZ124 ∷ CS34⁻ ∷ CX13 ∷ Bx0-1324 ∷ CCZ124 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS14 ∷ []) (CCZ134 ∷ Sb0-1-23-4 ∷ [])
  b3 = at 5 2 (CCZ124 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ314-at2332 c4) ▸
       at 1 2 (CCZ124 ∷ CX13 ∷ []) (lw0 c4 (CX13 ∷ CCZ124 ∷ []) (CCZ124 ∷ CX13 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (CCZ124 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ []) (lw0 c4 (CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ124 ∷ []) (CCZ124 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ []) tt tt Eq.refl) ▸
       at 1 2 [] (lw0 c4 (CCZ124 ∷ CCZ124 ∷ []) [] tt tt Eq.refl) ▸
       at 4 5 (Sb0-1-32-4 ∷ []) (refl) ▸
       at 4 2 (CS14 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS14-at2332 c4) ▸
       at 5 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 5 (CCZ134 ∷ []) (lw0 c4 (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸ done


-- auto CSd01 | BOX(1;2304): 5 steps
lem-auto-CSd01-∣-BOX⟨1·2304⟩ : Complete 4 → ⟪ (CS01⁻ ∷ Bx1-2304 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2304 ∷ CS01⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨1·2304⟩ c4 = run b0
  where
  b0 : Chain (CS01⁻ ∷ Bx1-2304 ∷ []) (Bx1-2304 ∷ CS01⁻ ∷ [])
  b0 = at 0 1 (CS01⁻ ∷ []) (lw4 c4 (CS01⁻ ∷ []) (CS01⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx1-2034 ∷ []) (lem-sym23-at01122330 c4) ▸
       at 0 2 (Bx1-2034 ∷ CS01⁻ ∷ []) (lem-CS20-beta-ci-at011220 c4) ▸
       at 0 1 (Bx1-2304 ∷ []) (lem-sym23-at011220 c4) ▸
       at 1 1 (CS01⁻ ∷ []) (lw4 c4 (CS01⁻ ∷ []) (CS01⁻ ∷ []) tt tt Eq.refl) ▸ done


-- auto CSd01 | BOX(1;2304) @1221: 7 steps
lem-auto-CSd01-∣-BOX⟨1·2304⟩-at1221 : Complete 4 → ⟪ (CS02⁻ ∷ Bx2-1304 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1304 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨1·2304⟩-at1221 c4 = run b0
  where
  b0 : Chain (CS02⁻ ∷ Bx2-1304 ∷ []) (Bx2-1304 ∷ CS02⁻ ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS01⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd02 c4) ▸
       at 2 2 (Bx1-2304 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·1304⟩ c4) ▸
       at 1 2 (Bx1-2304 ∷ CS01⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨1·2304⟩ c4) ▸
       at 0 2 (Bx2-1304 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·2304⟩ c4) ▸
       at 1 2 (CS02⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd01 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CSd01 | BOX(1;2304) @011220: 7 steps
lem-auto-CSd01-∣-BOX⟨1·2304⟩-at011220 : Complete 4 → ⟪ (CS12⁻ ∷ Bx2-0314 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0314 ∷ CS12⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨1·2304⟩-at011220 c4 = run b0
  where
  b0 : Chain (CS12⁻ ∷ Bx2-0314 ∷ []) (Bx2-0314 ∷ CS12⁻ ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS02⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS12⁻ ∷ []) (CS02⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx2-1304 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·0314⟩ c4) ▸
       at 1 2 (Bx2-1304 ∷ CS02⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨1·2304⟩-at1221 c4) ▸
       at 0 2 (Bx2-0314 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1304⟩ c4) ▸
       at 1 2 (CS12⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS02⁻ ∷ []) (CS12⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(2;0314): 3 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩ : Complete 4 → ⟪ (Sb⁻0-1-2-3 ∷ Bx2-0314 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0314 ∷ Sb⁻0-1-2-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩ c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-2-3 ∷ Bx2-0314 ∷ []) (Bx2-0314 ∷ Sb⁻0-1-2-3 ∷ [])
  b0 = at 0 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 2 (Bx2-0314 ∷ CS12⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨1·2304⟩-at011220 c4) ▸
       at 1 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸ done


-- sym12 @133441: 5 steps
lem-sym12-at133441 : Complete 4 → ⟪ (Bx0-3241 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ []) ⟫ʷ
lem-sym12-at133441 c4 = run b0
  where
  b0 : Chain (Bx0-3241 ∷ []) (Bx0-2341 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-3142 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·3241⟩ c4) ▸
       at 1 1 (Bx0-1342 ∷ []) (lem-sym12-at13213442 c4) ▸
       at 0 2 (Bx0-2341 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1342⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- T-beta @1221: 7 steps
lem-T-beta-at1221 : Complete 4 → ⟪ (Toff012 ∷ Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ Toff012 ∷ []) ⟫ʷ
lem-T-beta-at1221 c4 = run b0
  where
  b0 : Chain (Toff012 ∷ Bx0-2134 ∷ []) (Bx0-2134 ∷ Toff012 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff012 ∷ []) (Toff012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-1234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2134⟩ c4) ▸
       at 1 2 (Bx0-1234 ∷ Toff012 ∷ []) (lem-T-beta c4) ▸
       at 0 2 (Bx0-2134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1234⟩ c4) ▸
       at 1 2 (Toff012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff012 ∷ []) (Toff012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym12 @12233441: 5 steps
lem-sym12-at12233441 : Complete 4 → ⟪ (Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3241 ∷ []) ⟫ʷ
lem-sym12-at12233441 c4 = run b0
  where
  b0 : Chain (Bx0-2341 ∷ []) (Bx0-3241 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1342 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2341⟩ c4) ▸
       at 1 1 (Bx0-3142 ∷ []) (lem-sym12-at233442 c4) ▸
       at 0 2 (Bx0-3241 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·3142⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto TOFF012 | BOX(0;3241): 9 steps
lem-auto-TOFF012-∣-BOX⟨0·3241⟩ : Complete 4 → ⟪ (Toff012 ∷ Bx0-3241 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3241 ∷ Toff012 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-BOX⟨0·3241⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff012 ∷ Bx0-3241 ∷ []) (Bx0-3241 ∷ Toff012 ∷ [])
  b0 = at 0 1 (Toff012 ∷ []) (lw4 c4 (Toff012 ∷ []) (Toff012 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx0-2341 ∷ []) (lem-sym12-at133441 c4) ▸
       at 1 1 (Bx0-2314 ∷ []) (lem-sym34-at12233441 c4) ▸
       at 1 1 (Bx0-2134 ∷ []) (lem-sym23-at122331 c4) ▸
       at 0 2 (Bx0-2134 ∷ Toff012 ∷ []) (lem-T-beta-at1221 c4) ▸
       at 0 1 (Bx0-2314 ∷ []) (lem-sym23-at1221 c4) ▸
       at 0 1 (Bx0-2341 ∷ []) (lem-sym34-at122331 c4) ▸
       at 0 1 (Bx0-3241 ∷ []) (lem-sym12-at12233441 c4) ▸ done

  b1 : Chain (Bx0-3241 ∷ Toff012 ∷ []) (Bx0-3241 ∷ Toff012 ∷ [])
  b1 = at 1 1 (Toff012 ∷ []) (lw4 c4 (Toff012 ∷ []) (Toff012 ∷ []) tt tt Eq.refl) ▸ done


-- auto CS01 | BOX(1;2304): 5 steps
lem-auto-CS01-∣-BOX⟨1·2304⟩ : Complete 4 → ⟪ (CS01 ∷ Bx1-2304 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2304 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨1·2304⟩ c4 = run b0
  where
  b0 : Chain (CS01 ∷ Bx1-2304 ∷ []) (Bx1-2304 ∷ CS01 ∷ [])
  b0 = at 0 1 (CS01 ∷ []) (lw4 c4 (CS01 ∷ []) (CS01 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx1-2034 ∷ []) (lem-sym23-at01122330 c4) ▸
       at 0 2 (Bx1-2034 ∷ CS01 ∷ []) (lem-CS20-beta-c-at011220 c4) ▸
       at 0 1 (Bx1-2304 ∷ []) (lem-sym23-at011220 c4) ▸
       at 1 1 (CS01 ∷ []) (lw4 c4 (CS01 ∷ []) (CS01 ∷ []) tt tt Eq.refl) ▸ done


-- auto CS01 | BOX(1;2304) @1221: 7 steps
lem-auto-CS01-∣-BOX⟨1·2304⟩-at1221 : Complete 4 → ⟪ (CS02 ∷ Bx2-1304 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1304 ∷ CS02 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨1·2304⟩-at1221 c4 = run b0
  where
  b0 : Chain (CS02 ∷ Bx2-1304 ∷ []) (Bx2-1304 ∷ CS02 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS01 ∷ Sw12 ∷ []) (lem-nat-1-CS02 c4) ▸
       at 2 2 (Bx1-2304 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·1304⟩ c4) ▸
       at 1 2 (Bx1-2304 ∷ CS01 ∷ []) (lem-auto-CS01-∣-BOX⟨1·2304⟩ c4) ▸
       at 0 2 (Bx2-1304 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·2304⟩ c4) ▸
       at 1 2 (CS02 ∷ Sw12 ∷ []) (lem-nat-1-CS01 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CS01 | BOX(1;2304) @011220: 7 steps
lem-auto-CS01-∣-BOX⟨1·2304⟩-at011220 : Complete 4 → ⟪ (CS12 ∷ Bx2-0314 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0314 ∷ CS12 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨1·2304⟩-at011220 c4 = run b0
  where
  b0 : Chain (CS12 ∷ Bx2-0314 ∷ []) (Bx2-0314 ∷ CS12 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS02 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx2-1304 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·0314⟩ c4) ▸
       at 1 2 (Bx2-1304 ∷ CS02 ∷ []) (lem-auto-CS01-∣-BOX⟨1·2304⟩-at1221 c4) ▸
       at 0 2 (Bx2-0314 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1304⟩ c4) ▸
       at 1 2 (CS12 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS02 ∷ []) (CS12 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;2;3) | BOX(2;0314): 3 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩ : Complete 4 → ⟪ (Sb0-1-2-3 ∷ Bx2-0314 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0314 ∷ Sb0-1-2-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩ c4 = run b0
  where
  b0 : Chain (Sb0-1-2-3 ∷ Bx2-0314 ∷ []) (Bx2-0314 ∷ Sb0-1-2-3 ∷ [])
  b0 = at 0 1 (CS12 ∷ []) (refl) ▸
       at 0 2 (Bx2-0314 ∷ CS12 ∷ []) (lem-auto-CS01-∣-BOX⟨1·2304⟩-at011220 c4) ▸
       at 1 1 (Sb0-1-2-3 ∷ []) (refl) ▸ done


-- auto CCZ012 | CS34: 1 steps
lem-auto-CCZ012-∣-CS34 : Complete 4 → ⟪ (CCZ012 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CS34 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ CS34 ∷ []) (CS34 ∷ CCZ012 ∷ [])
  b0 = at 0 2 (CS34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CS)) ▸ done


-- auto CCZ012 | CS34 @3443: 7 steps
lem-auto-CCZ012-∣-CS34-at3443 : Complete 4 → ⟪ (CCZ012 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CS34-at3443 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ CS34 ∷ []) (CS34 ∷ CCZ012 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 2 2 (CS34 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CS34 ∷ []) (CS34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS34 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-CS34 c4) ▸
       at 0 2 (CS34 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CS34 ∷ []) (CS34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | CCZ341: 15 steps
lem-auto-CCZ012-∣-CCZ341 : Complete 4 → ⟪ (CCZ012 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ341 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ012 ∷ CCZ134 ∷ []) (CS13 ∷ CS02 ∷ CX12 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ CS34 ∷ [])
  b0 = at 1 1 (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (lw0 c4 (CCZ134 ∷ []) (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (CS13 ∷ CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ CS13 ∷ []) (CS13 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 5 4 (CX41 ∷ CS13⁻ ∷ CX41 ∷ CS01 ∷ []) (pw2 c4 (CS01 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) (CX41 ∷ CS13⁻ ∷ CX41 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 4 4 (CX41 ∷ CS13⁻ ∷ CX41 ∷ CX12 ∷ []) (lw0 c4 (CX12 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) (CX41 ∷ CS13⁻ ∷ CX41 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CX41 ∷ CS02⁻ ∷ []) (pw3 c4 (CS02⁻ ∷ CX41 ∷ []) (CX41 ∷ CS02⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS13⁻ ∷ CS02⁻ ∷ []) (lw4 c4 (CS02⁻ ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CS02⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CX41 ∷ CS02⁻ ∷ []) (pw3 c4 (CS02⁻ ∷ CX41 ∷ []) (CX41 ∷ CS02⁻ ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CS13 ∷ CS02 ∷ CX12 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ CS34 ∷ []) (CCZ134 ∷ CCZ012 ∷ [])
  b1 = at 2 4 (CX41 ∷ CS13⁻ ∷ CX41 ∷ CX12 ∷ []) (lw0 c4 (CX12 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) (CX41 ∷ CS13⁻ ∷ CX41 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CX41 ∷ CS02 ∷ []) (pw3 c4 (CS02 ∷ CX41 ∷ []) (CX41 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CS13⁻ ∷ CS02 ∷ []) (lw4 c4 (CS02 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CX41 ∷ CS02 ∷ []) (pw3 c4 (CS02 ∷ CX41 ∷ []) (CX41 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 4 5 (CCZ012 ∷ []) (lw4 c4 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS34 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-CS34-at3443 c4) ▸
       at 0 5 (CCZ134 ∷ []) (lw0 c4 (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ403: 11 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ403 : Complete 4 → ⟪ (Bx0-1234 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ403 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-1234 ∷ CCZ034 ∷ []) (CCZ034 ∷ Bx0-3124 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ []) (pw1 c4 (CCZ034 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
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
       at 0 1 (CCZ034 ∷ []) (pw1 c4 (CCZ034 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸ done


-- auto CCZ012 | CCZ324: 7 steps
lem-auto-CCZ012-∣-CCZ324 : Complete 4 → ⟪ (CCZ012 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ324 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ012 ∷ [])
  b0 = at 1 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (lw0 c4 (CCZ234 ∷ []) (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (CS34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CS)) ▸
       at 1 2 (CX24 ∷ CCZ012 ∷ []) (pw3 c4 (CCZ012 ∷ CX24 ∷ []) (CX24 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CS34⁻ ∷ CCZ012 ∷ []) (c₃ (CCZ) (CS • CS • CS)) ▸
       at 3 2 (CX24 ∷ CCZ012 ∷ []) (pw3 c4 (CCZ012 ∷ CX24 ∷ []) (CX24 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS23 ∷ CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ CS23 ∷ []) (CS23 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 0 5 (CCZ234 ∷ []) (lw0 c4 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸ done


-- auto CCZ012 | CCZ342: 15 steps
lem-auto-CCZ012-∣-CCZ342 : Complete 4 → ⟪ (CCZ012 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ342 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ012 ∷ CCZ234 ∷ []) (CS23 ∷ CS01 ∷ CX21 ∷ CX42 ∷ CS23⁻ ∷ CX42 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ CS34 ∷ [])
  b0 = at 1 1 (CS23 ∷ CX42 ∷ CS23⁻ ∷ CX42 ∷ CS34 ∷ []) (lw0 c4 (CCZ234 ∷ []) (CS23 ∷ CX42 ∷ CS23⁻ ∷ CX42 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (CS23 ∷ CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ CS23 ∷ []) (CS23 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 5 4 (CX42 ∷ CS23⁻ ∷ CX42 ∷ CS02 ∷ []) (pw1 c4 (CS02 ∷ CX42 ∷ CS23⁻ ∷ CX42 ∷ []) (CX42 ∷ CS23⁻ ∷ CX42 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 4 4 (CX42 ∷ CS23⁻ ∷ CX42 ∷ CX21 ∷ []) (lw0 c4 (CX21 ∷ CX42 ∷ CS23⁻ ∷ CX42 ∷ []) (CX42 ∷ CS23⁻ ∷ CX42 ∷ CX21 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CX42 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (Swap ↑ • CX₁₀ • Swap ↑)) ▸
       at 4 2 (CS23⁻ ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CS • CS • CS)) ▸
       at 5 2 (CX42 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (Swap ↑ • CX₁₀ • Swap ↑)) ▸ done

  b1 : Chain (CS23 ∷ CS01 ∷ CX21 ∷ CX42 ∷ CS23⁻ ∷ CX42 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ CS34 ∷ []) (CCZ234 ∷ CCZ012 ∷ [])
  b1 = at 2 4 (CX42 ∷ CS23⁻ ∷ CX42 ∷ CX21 ∷ []) (lw0 c4 (CX21 ∷ CX42 ∷ CS23⁻ ∷ CX42 ∷ []) (CX42 ∷ CS23⁻ ∷ CX42 ∷ CX21 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CX42 ∷ CS01 ∷ []) (c₂ (CS) (Swap ↑ • CX₁₀ • Swap ↑)) ▸
       at 2 2 (CS23⁻ ∷ CS01 ∷ []) (c₂ (CS) (CS • CS • CS)) ▸
       at 3 2 (CX42 ∷ CS01 ∷ []) (c₂ (CS) (Swap ↑ • CX₁₀ • Swap ↑)) ▸
       at 4 5 (CCZ012 ∷ []) (lw4 c4 (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS34 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-CS34-at3443 c4) ▸
       at 0 5 (CCZ234 ∷ []) (lw0 c4 (CS23 ∷ CX42 ∷ CS23⁻ ∷ CX42 ∷ CS34 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ401: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ401 : Complete 4 → ⟪ (Bx0-1234 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ401 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CCZ014 ∷ []) (CCZ014 ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ []) (pw2 c4 (CCZ014 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx0-1243 ∷ []) (lem-sym34 c4) ▸
       at 0 1 (Bx0-1423 ∷ []) (lem-sym23-at3443 c4) ▸
       at 0 2 (CCZ014 ∷ Bx0-1423 ∷ []) (sym (lem-Cz-beta-at243243 c4)) ▸
       at 1 1 (Bx0-1243 ∷ []) (lem-sym23-at243243 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym34-at3443 c4) ▸
       at 0 1 (CCZ014 ∷ []) (pw2 c4 (CCZ014 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ402: 9 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ402 : Complete 4 → ⟪ (Bx0-1234 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ402 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-1234 ∷ CCZ024 ∷ []) (CCZ024 ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 0 1 (Bx0-2143 ∷ []) (lem-sym34-at1221 c4) ▸
       at 0 1 (Bx0-2413 ∷ []) (lem-sym23-at12213443 c4) ▸
       at 0 2 (CCZ024 ∷ Bx0-2413 ∷ []) (sym (lem-Cz-beta-at12243143 c4)) ▸
       at 1 1 (Bx0-2143 ∷ []) (lem-sym23-at12243143 c4) ▸
       at 1 1 (Bx0-2134 ∷ []) (lem-sym34-at12213443 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸ done

  b1 : Chain (CCZ024 ∷ Bx0-1234 ∷ []) (CCZ024 ∷ Bx0-1234 ∷ [])
  b1 = at 0 1 (CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ132: 5 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ132 : Complete 4 → ⟪ (Bx0-1234 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ132 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CCZ123 ∷ []) (CCZ123 ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx0-1243 ∷ []) (lem-sym34 c4) ▸
       at 0 2 (CCZ123 ∷ Bx0-1243 ∷ []) (sym (lem-c124-beta-at3443 c4)) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym34-at3443 c4) ▸
       at 0 1 (CCZ123 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸ done


-- beta-T @04203243: 8 steps
lem-beta-T-at04203243 : Complete 4 → ⟪ (Bx4-1023 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ []) ⟫ʷ
lem-beta-T-at04203243 c4 = run b0
  where
  b0 : Chain (Bx4-1023 ∷ []) (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-0123 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·1023⟩ c4) ▸
       at 1 1 (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ []) (lem-beta-T-at0410213243 c4) ▸
       at 0 2 (Toff401 ∷ Sw01 ∷ []) (lem-nat-0-TOFF401 c4) ▸
       at 1 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 2 2 (Toff401 ∷ Sw01 ∷ []) (lem-nat-0-TOFF401 c4) ▸
       at 3 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 4 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- beta-T @0412203143: 8 steps
lem-beta-T-at0412203143 : Complete 4 → ⟪ (Bx4-2013 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ134 ∷ []) ⟫ʷ
lem-beta-T-at0412203143 c4 = run b0
  where
  b0 : Chain (Bx4-2013 ∷ []) (Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ134 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-1023 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·2013⟩ c4) ▸
       at 1 1 (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ []) (lem-beta-T-at04203243 c4) ▸
       at 0 2 (Toff402 ∷ Sw12 ∷ []) (lem-nat-1-TOFF401 c4) ▸
       at 1 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff402 ∷ Sw12 ∷ []) (lem-nat-1-TOFF401 c4) ▸
       at 3 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- beta-T @0413203142: 8 steps
lem-beta-T-at0413203142 : Complete 4 → ⟪ (Bx4-3012 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ []) ⟫ʷ
lem-beta-T-at0413203142 c4 = run b0
  where
  b0 : Chain (Bx4-3012 ∷ []) (Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-2013 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·3012⟩ c4) ▸
       at 1 1 (Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ134 ∷ []) (lem-beta-T-at0412203143 c4) ▸
       at 0 2 (Toff403 ∷ Sw23 ∷ []) (lem-nat-2-TOFF402 c4) ▸
       at 1 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 2 2 (Toff403 ∷ Sw23 ∷ []) (lem-nat-2-TOFF402 c4) ▸
       at 3 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 4 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- beta-T @0413213042: 8 steps
lem-beta-T-at0413213042 : Complete 4 → ⟪ (Bx4-3102 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ []) ⟫ʷ
lem-beta-T-at0413213042 c4 = run b0
  where
  b0 : Chain (Bx4-3102 ∷ []) (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-3012 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·3102⟩ c4) ▸
       at 1 1 (Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ []) (lem-beta-T-at0413203142 c4) ▸
       at 0 2 (Toff413 ∷ Sw01 ∷ []) (lem-nat-0-TOFF403 c4) ▸
       at 1 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 2 2 (Toff413 ∷ Sw01 ∷ []) (lem-nat-0-TOFF403 c4) ▸
       at 3 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 4 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | CCZ342 @0110: 7 steps
lem-auto-CCZ012-∣-CCZ342-at0110 : Complete 4 → ⟪ (CCZ012 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ342-at0110 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ012 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 1 2 (CCZ234 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-CCZ342 c4) ▸
       at 0 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 1 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | CCZ342 @021021: 7 steps
lem-auto-CCZ012-∣-CCZ342-at021021 : Complete 4 → ⟪ (CCZ012 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ342-at021021 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ012 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ134 ∷ []) (CCZ234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ234 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-CCZ342-at0110 c4) ▸
       at 0 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | CCZ342 @03102132: 7 steps
lem-auto-CCZ012-∣-CCZ342-at03102132 : Complete 4 → ⟪ (CCZ013 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CCZ013 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ342-at03102132 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ013 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 2 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 1 2 (CCZ134 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-CCZ342-at021021 c4) ▸
       at 0 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 1 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | CCZ342 @0410213243: 7 steps
lem-auto-CCZ012-∣-CCZ342-at0410213243 : Complete 4 → ⟪ (CCZ014 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CCZ014 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ342-at0410213243 c4 = run b0
  where
  b0 : Chain (CCZ014 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ014 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 2 2 (CCZ124 ∷ Sw34 ∷ []) (lem-nat-3-CCZ123 c4) ▸
       at 1 2 (CCZ124 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-CCZ342-at03102132 c4) ▸
       at 0 2 (CCZ123 ∷ Sw34 ∷ []) (lem-nat-3-CCZ124 c4) ▸
       at 1 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | CCZ342 @04103143: 7 steps
lem-auto-CCZ012-∣-CCZ342-at04103143 : Complete 4 → ⟪ (CCZ024 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CCZ024 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ342-at04103143 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ024 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 2 2 (CCZ123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ123 ∷ CCZ014 ∷ []) (lem-auto-CCZ012-∣-CCZ342-at0410213243 c4) ▸
       at 0 2 (CCZ123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | BOX(4;0312): 31 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨4·0312⟩ : Complete 4 → ⟪ (Bx0-1234 ∷ Bx4-0312 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0312 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨4·0312⟩ c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Bx0-1234 ∷ Bx4-0312 ∷ []) (Toff413 ∷ Toff413 ∷ Bx0-1342 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ [])
  b0 = at 1 1 (Bx4-3012 ∷ []) (lem-sym12-at0410233142 c4) ▸
       at 1 1 (Bx4-3102 ∷ []) (lem-sym23-at0413203142 c4) ▸
       at 1 1 (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ []) (lem-beta-T-at0413213042 c4) ▸
       at 0 0 (Toff413 ∷ Toff413 ∷ []) (lw0 c4 [] (Toff413 ∷ Toff413 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Toff413 ∷ []) (lw0 c4 (Toff413 ∷ []) (Toff413 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Toff413 ∷ []) (lw0 c4 (Toff413 ∷ []) (Toff413 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 2 1 (Bx0-1342 ∷ []) (lem-sym34-at2332 c4) ▸ done

  b1 : Chain (Toff413 ∷ Toff413 ∷ Bx0-1342 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ []) (Toff413 ∷ CCZ123 ∷ CCZ024 ∷ Toff413 ∷ Toff413 ∷ Bx0-1234 ∷ Toff413 ∷ CCZ024 ∷ [])
  b1 = at 1 3 (Bx0-1342 ∷ CCZ123 ∷ []) (lem-T312-beta-at233442 c4) ▸
       at 1 1 (Bx0-1324 ∷ []) (lem-sym34-at233442 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸
       at 1 2 (CCZ123 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ132 c4) ▸
       at 2 2 (CCZ024 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ402 c4) ▸
       at 3 0 (Toff413 ∷ Toff413 ∷ []) (lw0 c4 [] (Toff413 ∷ Toff413 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Toff413 ∷ []) (lw0 c4 (Toff413 ∷ []) (Toff413 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Toff413 ∷ []) (lw0 c4 (Toff413 ∷ []) (Toff413 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Toff413 ∷ CCZ123 ∷ CCZ024 ∷ Toff413 ∷ Toff413 ∷ Bx0-1234 ∷ Toff413 ∷ CCZ024 ∷ []) (CCZ123 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ123 ∷ CCZ024 ∷ Bx0-1234 ∷ [])
  b2 = at 5 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 5 1 (Bx0-1342 ∷ []) (lem-sym34-at2332 c4) ▸
       at 4 3 (Bx0-1342 ∷ CCZ123 ∷ []) (lem-T312-beta-at233442 c4) ▸
       at 4 1 (Bx0-1324 ∷ []) (lem-sym34-at233442 c4) ▸
       at 4 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸
       at 4 2 (CCZ123 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ132 c4) ▸
       at 5 2 (CCZ024 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ402 c4) ▸
       at 0 2 (CCZ123 ∷ Toff413 ∷ []) (lw0 c4 (Toff413 ∷ CCZ123 ∷ []) (CCZ123 ∷ Toff413 ∷ []) tt tt Eq.refl) ▸ done

  b3 : Chain (CCZ123 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ123 ∷ CCZ024 ∷ Bx0-1234 ∷ []) (Bx4-0312 ∷ Bx0-1234 ∷ [])
  b3 = at 3 2 (CCZ123 ∷ Toff413 ∷ []) (lw0 c4 (Toff413 ∷ CCZ123 ∷ []) (CCZ123 ∷ Toff413 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ123 ∷ CCZ024 ∷ []) (lem-auto-CCZ012-∣-CCZ342-at04103143 c4) ▸
       at 1 2 (CCZ123 ∷ Toff413 ∷ []) (lw0 c4 (Toff413 ∷ CCZ123 ∷ []) (CCZ123 ∷ Toff413 ∷ []) tt tt Eq.refl) ▸
       at 0 2 [] (lw4 c4 (CCZ123 ∷ CCZ123 ∷ []) [] tt tt Eq.refl) ▸
       at 0 4 (Bx4-3102 ∷ []) (sym (lem-beta-T-at0413213042 c4)) ▸
       at 0 1 (Bx4-3012 ∷ []) (lem-sym23-at0413213042 c4) ▸
       at 0 1 (Bx4-0312 ∷ []) (lem-sym12-at0413203142 c4) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(2;0314) @2332: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩-at2332 : Complete 4 → ⟪ (Sb⁻0-1-3-2 ∷ Bx3-0214 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0214 ∷ Sb⁻0-1-3-2 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-3-2 ∷ Bx3-0214 ∷ []) (Bx3-0214 ∷ Sb⁻0-1-3-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·3·2⟩ c4) ▸
       at 2 2 (Bx2-0314 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0214⟩ c4) ▸
       at 1 2 (Bx2-0314 ∷ Sb⁻0-1-2-3 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩ c4) ▸
       at 0 2 (Bx3-0214 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0314⟩ c4) ▸
       at 1 2 (Sb⁻0-1-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·2·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(2;0314) @243243: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩-at243243 : Complete 4 → ⟪ (Sb⁻0-1-4-2 ∷ Bx4-0213 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0213 ∷ Sb⁻0-1-4-2 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-4-2 ∷ Bx4-0213 ∷ []) (Bx4-0213 ∷ Sb⁻0-1-4-2 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-3-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·4·2⟩ c4) ▸
       at 2 2 (Bx3-0214 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·0213⟩ c4) ▸
       at 1 2 (Bx3-0214 ∷ Sb⁻0-1-3-2 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩-at2332 c4) ▸
       at 0 2 (Bx4-0213 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·0214⟩ c4) ▸
       at 1 2 (Sb⁻0-1-4-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·3·2⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(2;0314) @2442: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩-at2442 : Complete 4 → ⟪ (Sb⁻0-1-4-3 ∷ Bx4-0312 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0312 ∷ Sb⁻0-1-4-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩-at2442 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-4-3 ∷ Bx4-0312 ∷ []) (Bx4-0312 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·4·3⟩ c4) ▸
       at 2 2 (Bx4-0213 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0312⟩ c4) ▸
       at 1 2 (Bx4-0213 ∷ Sb⁻0-1-4-2 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩-at243243 c4) ▸
       at 0 2 (Bx4-0312 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0213⟩ c4) ▸
       at 1 2 (Sb⁻0-1-4-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·4·2⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto TOFF012 | BOX(0;3241) @0110: 7 steps
lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at0110 : Complete 4 → ⟪ (Toff102 ∷ Bx1-3240 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3240 ∷ Toff102 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at0110 c4 = run b0
  where
  b0 : Chain (Toff102 ∷ Bx1-3240 ∷ []) (Bx1-3240 ∷ Toff102 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff102 ∷ []) (Toff012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-3241 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·3240⟩ c4) ▸
       at 1 2 (Bx0-3241 ∷ Toff012 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·3241⟩ c4) ▸
       at 0 2 (Bx1-3240 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·3241⟩ c4) ▸
       at 1 2 (Toff102 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff012 ∷ []) (Toff102 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto TOFF012 | BOX(0;3241) @021021: 7 steps
lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at021021 : Complete 4 → ⟪ (Toff201 ∷ Bx2-3140 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3140 ∷ Toff201 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at021021 c4 = run b0
  where
  b0 : Chain (Toff201 ∷ Bx2-3140 ∷ []) (Bx2-3140 ∷ Toff201 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff102 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff201 ∷ []) (Toff102 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx1-3240 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·3140⟩ c4) ▸
       at 1 2 (Bx1-3240 ∷ Toff102 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at0110 c4) ▸
       at 0 2 (Bx2-3140 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·3240⟩ c4) ▸
       at 1 2 (Toff201 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff102 ∷ []) (Toff201 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto TOFF012 | BOX(0;3241) @03102132: 7 steps
lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at03102132 : Complete 4 → ⟪ (Toff301 ∷ Bx3-2140 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2140 ∷ Toff301 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at03102132 c4 = run b0
  where
  b0 : Chain (Toff301 ∷ Bx3-2140 ∷ []) (Bx3-2140 ∷ Toff301 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff201 ∷ Sw23 ∷ []) (lem-nat-2-TOFF301 c4) ▸
       at 2 2 (Bx2-3140 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·2140⟩ c4) ▸
       at 1 2 (Bx2-3140 ∷ Toff201 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at021021 c4) ▸
       at 0 2 (Bx3-2140 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·3140⟩ c4) ▸
       at 1 2 (Toff301 ∷ Sw23 ∷ []) (lem-nat-2-TOFF201 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto TOFF012 | BOX(0;3241) @0410213243: 7 steps
lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at0410213243 : Complete 4 → ⟪ (Toff401 ∷ Bx4-2130 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2130 ∷ Toff401 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at0410213243 c4 = run b0
  where
  b0 : Chain (Toff401 ∷ Bx4-2130 ∷ []) (Bx4-2130 ∷ Toff401 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff301 ∷ Sw34 ∷ []) (lem-nat-3-TOFF401 c4) ▸
       at 2 2 (Bx3-2140 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·2130⟩ c4) ▸
       at 1 2 (Bx3-2140 ∷ Toff301 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at03102132 c4) ▸
       at 0 2 (Bx4-2130 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·2140⟩ c4) ▸
       at 1 2 (Toff401 ∷ Sw34 ∷ []) (lem-nat-3-TOFF301 c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto TOFF012 | BOX(0;3241) @04103143: 7 steps
lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at04103143 : Complete 4 → ⟪ (Toff402 ∷ Bx4-1230 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1230 ∷ Toff402 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at04103143 c4 = run b0
  where
  b0 : Chain (Toff402 ∷ Bx4-1230 ∷ []) (Bx4-1230 ∷ Toff402 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff401 ∷ Sw12 ∷ []) (lem-nat-1-TOFF402 c4) ▸
       at 2 2 (Bx4-2130 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·1230⟩ c4) ▸
       at 1 2 (Bx4-2130 ∷ Toff401 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at0410213243 c4) ▸
       at 0 2 (Bx4-1230 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·2130⟩ c4) ▸
       at 1 2 (Toff402 ∷ Sw12 ∷ []) (lem-nat-1-TOFF401 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto TOFF012 | BOX(0;3241) @0410233142: 7 steps
lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at0410233142 : Complete 4 → ⟪ (Toff403 ∷ Bx4-1320 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1320 ∷ Toff403 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at0410233142 c4 = run b0
  where
  b0 : Chain (Toff403 ∷ Bx4-1320 ∷ []) (Bx4-1320 ∷ Toff403 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff402 ∷ Sw23 ∷ []) (lem-nat-2-TOFF403 c4) ▸
       at 2 2 (Bx4-1230 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·1320⟩ c4) ▸
       at 1 2 (Bx4-1230 ∷ Toff402 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at04103143 c4) ▸
       at 0 2 (Bx4-1320 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·1230⟩ c4) ▸
       at 1 2 (Toff403 ∷ Sw23 ∷ []) (lem-nat-2-TOFF402 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto TOFF012 | BOX(0;3241) @04233042: 7 steps
lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at04233042 : Complete 4 → ⟪ (Toff413 ∷ Bx4-0321 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0321 ∷ Toff413 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at04233042 c4 = run b0
  where
  b0 : Chain (Toff413 ∷ Bx4-0321 ∷ []) (Bx4-0321 ∷ Toff413 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff403 ∷ Sw01 ∷ []) (lem-nat-0-TOFF413 c4) ▸
       at 2 2 (Bx4-1320 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·0321⟩ c4) ▸
       at 1 2 (Bx4-1320 ∷ Toff403 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at0410233142 c4) ▸
       at 0 2 (Bx4-0321 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·1320⟩ c4) ▸
       at 1 2 (Toff413 ∷ Sw01 ∷ []) (lem-nat-0-TOFF403 c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto TOFF012 | BOX(0;3241) @0412233041: 7 steps
lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at0412233041 : Complete 4 → ⟪ (Toff423 ∷ Bx4-0312 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0312 ∷ Toff423 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at0412233041 c4 = run b0
  where
  b0 : Chain (Toff423 ∷ Bx4-0312 ∷ []) (Bx4-0312 ∷ Toff423 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff413 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff423 ∷ []) (Toff413 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx4-0321 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0312⟩ c4) ▸
       at 1 2 (Bx4-0321 ∷ Toff413 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·3241⟩-at04233042 c4) ▸
       at 0 2 (Bx4-0312 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0321⟩ c4) ▸
       at 1 2 (Toff423 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff413 ∷ []) (Toff423 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;2;3) | BOX(2;0314) @2332: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩-at2332 : Complete 4 → ⟪ (Sb0-1-3-2 ∷ Bx3-0214 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0214 ∷ Sb0-1-3-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-3-2 ∷ Bx3-0214 ∷ []) (Bx3-0214 ∷ Sb0-1-3-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·3·2⟩ c4) ▸
       at 2 2 (Bx2-0314 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0214⟩ c4) ▸
       at 1 2 (Bx2-0314 ∷ Sb0-1-2-3 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩ c4) ▸
       at 0 2 (Bx3-0214 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0314⟩ c4) ▸
       at 1 2 (Sb0-1-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·2·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;2;3) | BOX(2;0314) @243243: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩-at243243 : Complete 4 → ⟪ (Sb0-1-4-2 ∷ Bx4-0213 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0213 ∷ Sb0-1-4-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-4-2 ∷ Bx4-0213 ∷ []) (Bx4-0213 ∷ Sb0-1-4-2 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-3-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·4·2⟩ c4) ▸
       at 2 2 (Bx3-0214 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·0213⟩ c4) ▸
       at 1 2 (Bx3-0214 ∷ Sb0-1-3-2 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0314⟩-at2332 c4) ▸
       at 0 2 (Bx4-0213 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·0214⟩ c4) ▸
       at 1 2 (Sb0-1-4-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·3·2⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


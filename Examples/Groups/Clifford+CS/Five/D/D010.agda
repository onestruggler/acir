{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D010 where

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
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-CS20-beta-c ; lem-CS20-beta-ci ; lem-CSd12-beta ; lem-CX23-beta ; lem-sym12 ; lem-sym23 ; lem-sym34)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-beta-T-at1221 ; lem-sym12-at1221 ; lem-sym12-at132132 ; lem-sym23-at1221 ; lem-sym34-at1221)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-beta-T-at122331 ; lem-sym23-at12213443 ; lem-sym23-at122331 ; lem-sym23-at12243143 ; lem-sym23-at2332 ; lem-sym23-at243243 ; lem-sym23-at3443 ; lem-sym34-at12213443 ; lem-sym34-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-CS20-beta-c-at1221 ; lem-sym12-at2332 ; lem-sym23-at021021 ; lem-sym34-at122331 ; lem-sym34-at12233441)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-CX23-beta-at2332 ; lem-auto-BOX⟨0·1234⟩-∣-CS14 ; lem-auto-BOX⟨0·1234⟩-∣-CSd14)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at2332 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at2332 ; lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩)
open import Examples.Groups.Clifford+CS.Five.D.D007 using (lem-CS12-beta-at12243143 ; lem-SBsym-at0113203442 ; lem-T312-beta-at12233441 ; lem-auto-BOX⟨0·1234⟩-∣-BOX⟨0·1234⟩ ; lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩ ; lem-sym23-at02102331)
open import Examples.Groups.Clifford+CS.Five.D.D008 using (lem-auto-TOFF012-∣-CS34-at0412233041)
open import Examples.Groups.Clifford+CS.Five.D.D009 using (lem-CS20-beta-c-at243243 ; lem-CS20-beta-ci-at243243 ; lem-CX23-beta-at1221 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ314-at2332 ; lem-auto-BOX⟨0·1234⟩-∣-CSd20 ; lem-auto-BOX⟨0·1234⟩-∣-CSd30-at2332 ; lem-auto-CCZ012-∣-BOX⟨3·0142⟩ ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CS10-at2332 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CS20-at2332 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CS30-at2332 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at2332 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd0-at2332)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-BOX⟨0·2134⟩ ; lem-nat-2-BOX⟨0·1234⟩ ; lem-nat-2-BOX⟨0·1324⟩ ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ013 ; lem-nat-3-BOX⟨0·1423⟩)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-3-BOX⟨0·1324⟩)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-CCZ014)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-0-CCZ034)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-1-BOX⟨0·1234⟩)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-0-BOX⟨0·1234⟩ ; lem-nat-0-BOX⟨1·0234⟩ ; lem-nat-1-BOX⟨1·0234⟩ ; lem-nat-1-BOX⟨2·0134⟩)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-nat-0-BOX⟨0·2134⟩ ; lem-nat-0-BOX⟨1·2034⟩)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-nat-0-BOX⟨0·2314⟩ ; lem-nat-0-BOX⟨1·2304⟩)
open import Examples.Groups.Clifford+CS.Five.D.R013 using (lem-nat-0-BOX⟨0·1324⟩ ; lem-nat-1-BOX⟨1·0324⟩)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-1-CSd02 ; lem-nat-2-BOX⟨0·1432⟩ ; lem-nat-2-CSd02 ; lem-nat-2-SBOX⟨0·1·23·4⟩ ; lem-nat-2-SBOX⟨0·1·32·4⟩ ; lem-nat-2-SBOX⟨0·1·4·2⟩ ; lem-nat-2-SBOX⟨0·1·4·3⟩ ; lem-nat-2-SBOXd⟨0·1·4·2⟩ ; lem-nat-2-SBOXd⟨0·1·4·3⟩ ; lem-nat-3-SBOX⟨0·1·3·2⟩ ; lem-nat-3-SBOX⟨0·1·4·2⟩ ; lem-nat-3-SBOXd⟨0·1·3·2⟩ ; lem-nat-3-SBOXd⟨0·1·4·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-0-BOX⟨1·2340⟩ ; lem-nat-1-CSd01)
open import Examples.Groups.Clifford+CS.Five.D.R016 using (lem-nat-0-BOX⟨1·0324⟩ ; lem-nat-1-BOX⟨2·0314⟩)
open import Examples.Groups.Clifford+CS.Five.D.R019 using (lem-comm-CSd02-CCZ134 ; lem-comm-CSd03-CCZ124 ; lem-nat-0-BOX⟨0·2341⟩ ; lem-nat-0-BOX⟨0·3124⟩ ; lem-nat-0-BOX⟨1·3024⟩ ; lem-nat-0-BOX⟨2·0134⟩ ; lem-nat-0-BOX⟨2·0314⟩ ; lem-nat-0-BOX⟨2·1034⟩ ; lem-nat-0-BOX⟨2·1304⟩ ; lem-nat-0-BOX⟨2·3014⟩ ; lem-nat-0-BOX⟨2·3104⟩ ; lem-nat-1-BOX⟨1·3024⟩ ; lem-nat-1-BOX⟨2·3014⟩ ; lem-nat-2-BOX⟨0·1423⟩ ; lem-nat-2-CSd03 ; lem-nat-2-SBOX⟨0·1·2·3⟩ ; lem-nat-2-SBOX⟨0·1·3·2⟩ ; lem-nat-2-SBOXd⟨0·1·2·3⟩ ; lem-nat-2-SBOXd⟨0·1·3·2⟩)
-- auto BOX(0;1234) | CSd20 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd20-at2332 : Complete 4 → ⟪ (Bx0-1324 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd20-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ c4) ▸
       at 2 2 (CS02⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd03 c4) ▸
       at 1 2 (CS02⁻ ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd20 c4) ▸
       at 0 2 (CS03⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd02 c4) ▸
       at 1 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CCZ013: 64 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ013 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ013 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (Sb0-1-23-4 ∷ CCZ013 ∷ []) (CS03 ∷ Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ K4 ∷ CCZ234 ∷ K4⁻ ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ Sb⁻0-1-4-2 ∷ CS01 ∷ [])
  b0 = at 1 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (lw4 c4 (CCZ013 ∷ []) (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS03 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS20-at2332 c4) ▸
       at 1 1 (Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ []) (refl) ▸
       at 5 1 (CS14⁻ ∷ []) (refl) ▸
       at 5 4 (CX13 ∷ CS03⁻ ∷ CX13 ∷ CS14⁻ ∷ []) (pw2 c4 (CS14⁻ ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ []) (CX13 ∷ CS03⁻ ∷ CX13 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 8 1 (Sb⁻0-1-4-2 ∷ []) (refl) ▸
       at 4 1 (K4 ∷ CCZ234 ∷ K4⁻ ∷ []) (lw0 c4 (Toff423 ∷ []) (K4 ∷ CCZ234 ∷ K4⁻ ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CS03 ∷ Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ K4 ∷ CCZ234 ∷ K4⁻ ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ Sb⁻0-1-4-2 ∷ CS01 ∷ []) (CS03 ∷ Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ K4 ∷ CS24 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ K4⁻ ∷ Sb⁻0-1-4-2 ∷ CS01 ∷ [])
  b1 = at 6 4 (CX13 ∷ CS03⁻ ∷ CX13 ∷ K4⁻ ∷ []) (pw2 c4 (K4⁻ ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ []) (CX13 ∷ CS03⁻ ∷ CX13 ∷ K4⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ []) (lw0 c4 (CCZ234 ∷ []) (CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 9 4 (CX13 ∷ CS03⁻ ∷ CX13 ∷ CS34 ∷ []) (pw2 c4 (CS34 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ []) (CX13 ∷ CS03⁻ ∷ CX13 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 8 4 (CX13 ∷ CS03⁻ ∷ CX13 ∷ CX32 ∷ []) (lw4 c4 (CX32 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ []) (CX13 ∷ CS03⁻ ∷ CX13 ∷ CX32 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CX13 ∷ CS24⁻ ∷ []) (lw0 c4 (CS24⁻ ∷ CX13 ∷ []) (CX13 ∷ CS24⁻ ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CS03⁻ ∷ CS24⁻ ∷ []) (pw1 c4 (CS24⁻ ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CS24⁻ ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CX13 ∷ CS24⁻ ∷ []) (lw0 c4 (CS24⁻ ∷ CX13 ∷ []) (CX13 ∷ CS24⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 4 (CX13 ∷ CS03⁻ ∷ CX13 ∷ CX32 ∷ []) (lw4 c4 (CX32 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ []) (CX13 ∷ CS03⁻ ∷ CX13 ∷ CX32 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (CS03 ∷ Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ K4 ∷ CS24 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ K4⁻ ∷ Sb⁻0-1-4-2 ∷ CS01 ∷ []) (CS03 ∷ Bx0-1324 ∷ Toff423 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS14 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS01 ∷ [])
  b2 = at 5 2 (CX13 ∷ CS24 ∷ []) (lw0 c4 (CS24 ∷ CX13 ∷ []) (CX13 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CS03⁻ ∷ CS24 ∷ []) (pw1 c4 (CS24 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CX13 ∷ CS24 ∷ []) (lw0 c4 (CS24 ∷ CX13 ∷ []) (CX13 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 8 5 (CCZ234 ∷ []) (lw0 c4 (CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 4 4 (CX13 ∷ CS03⁻ ∷ CX13 ∷ K4 ∷ []) (pw2 c4 (K4 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ []) (CX13 ∷ CS03⁻ ∷ CX13 ∷ K4 ∷ []) tt tt Eq.refl) ▸
       at 7 3 (Toff423 ∷ []) (lw0 c4 (K4 ∷ CCZ234 ∷ K4⁻ ∷ []) (Toff423 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CS14 ∷ []) (refl) ▸
       at 3 4 (CX13 ∷ CS03⁻ ∷ CX13 ∷ CS14 ∷ []) (pw2 c4 (CS14 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ []) (CX13 ∷ CS03⁻ ∷ CX13 ∷ CS14 ∷ []) tt tt Eq.refl) ▸ done

  b3 : Chain (CS03 ∷ Bx0-1324 ∷ Toff423 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS14 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS01 ∷ []) (CS03 ∷ Bx0-1324 ∷ K4 ∷ CS24 ∷ CX32 ∷ CX13 ∷ CS03⁻ ∷ CS24⁻ ∷ CX13 ∷ CX32 ∷ CS34 ∷ K4⁻ ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS01 ∷ [])
  b3 = at 6 1 (Sb0-1-4-2 ∷ []) (refl) ▸
       at 2 1 (K4 ∷ CCZ234 ∷ K4⁻ ∷ []) (lw0 c4 (Toff423 ∷ []) (K4 ∷ CCZ234 ∷ K4⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 4 (CX13 ∷ CS03⁻ ∷ CX13 ∷ K4⁻ ∷ []) (pw2 c4 (K4⁻ ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ []) (CX13 ∷ CS03⁻ ∷ CX13 ∷ K4⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ []) (lw0 c4 (CCZ234 ∷ []) (CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 7 4 (CX13 ∷ CS03⁻ ∷ CX13 ∷ CS34 ∷ []) (pw2 c4 (CS34 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ []) (CX13 ∷ CS03⁻ ∷ CX13 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 6 4 (CX13 ∷ CS03⁻ ∷ CX13 ∷ CX32 ∷ []) (lw4 c4 (CX32 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ []) (CX13 ∷ CS03⁻ ∷ CX13 ∷ CX32 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CX13 ∷ CS24⁻ ∷ []) (lw0 c4 (CS24⁻ ∷ CX13 ∷ []) (CX13 ∷ CS24⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CS03⁻ ∷ CS24⁻ ∷ []) (pw1 c4 (CS24⁻ ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CS24⁻ ∷ []) tt tt Eq.refl) ▸ done

  b4 : Chain (CS03 ∷ Bx0-1324 ∷ K4 ∷ CS24 ∷ CX32 ∷ CX13 ∷ CS03⁻ ∷ CS24⁻ ∷ CX13 ∷ CX32 ∷ CS34 ∷ K4⁻ ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS01 ∷ []) (CS03 ∷ Bx0-1324 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS01 ∷ [])
  b4 = at 7 2 (CX13 ∷ CS24⁻ ∷ []) (lw0 c4 (CS24⁻ ∷ CX13 ∷ []) (CX13 ∷ CS24⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 4 (CX13 ∷ CS03⁻ ∷ CX13 ∷ CX32 ∷ []) (lw4 c4 (CX32 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ []) (CX13 ∷ CS03⁻ ∷ CX13 ∷ CX32 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CX13 ∷ CS24 ∷ []) (lw0 c4 (CS24 ∷ CX13 ∷ []) (CX13 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS03⁻ ∷ CS24 ∷ []) (pw1 c4 (CS24 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CX13 ∷ CS24 ∷ []) (lw0 c4 (CS24 ∷ CX13 ∷ []) (CX13 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 6 5 (CCZ234 ∷ []) (lw0 c4 (CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (CX13 ∷ CS03⁻ ∷ CX13 ∷ K4 ∷ []) (pw2 c4 (K4 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ []) (CX13 ∷ CS03⁻ ∷ CX13 ∷ K4 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (Toff423 ∷ []) (lw0 c4 (K4 ∷ CCZ234 ∷ K4⁻ ∷ []) (Toff423 ∷ []) tt tt Eq.refl) ▸ done

  b5 : Chain (CS03 ∷ Bx0-1324 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS01 ∷ []) (CS03 ∷ CX13 ∷ CCZ124 ∷ CS03⁻ ∷ Bx0-1324 ∷ CX13 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS01 ∷ [])
  b5 = at 1 0 (CX13 ∷ CX13 ∷ []) (lw4 c4 [] (CX13 ∷ CX13 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸
       at 3 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 2 3 (Bx0-2134 ∷ CCZ124 ∷ []) (lem-CX23-beta-at1221 c4) ▸
       at 2 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸
       at 2 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 2 2 (CCZ124 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ314-at2332 c4) ▸
       at 3 2 (CS03⁻ ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd20-at2332 c4) ▸ done

  b6 : Chain (CS03 ∷ CX13 ∷ CCZ124 ∷ CS03⁻ ∷ Bx0-1324 ∷ CX13 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS01 ∷ []) (CS03 ∷ CCZ124 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CCZ124 ∷ Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS01 ∷ [])
  b6 = at 4 0 (CX13 ∷ CX13 ∷ []) (lw4 c4 [] (CX13 ∷ CX13 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸
       at 6 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 5 3 (Bx0-2134 ∷ CCZ124 ∷ []) (lem-CX23-beta-at1221 c4) ▸
       at 5 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸
       at 5 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 5 2 (CCZ124 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ314-at2332 c4) ▸
       at 1 2 (CCZ124 ∷ CX13 ∷ []) (lw0 c4 (CX13 ∷ CCZ124 ∷ []) (CCZ124 ∷ CX13 ∷ []) tt tt Eq.refl) ▸ done

  b7 : Chain (CS03 ∷ CCZ124 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CCZ124 ∷ Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS01 ∷ []) (CCZ013 ∷ Sb0-1-23-4 ∷ [])
  b7 = at 4 2 (CCZ124 ∷ CX13 ∷ []) (lw0 c4 (CX13 ∷ CCZ124 ∷ []) (CCZ124 ∷ CX13 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ124 ∷ CS03⁻ ∷ []) (lem-comm-CSd03-CCZ124 c4) ▸
       at 2 2 (CCZ124 ∷ CX13 ∷ []) (lw0 c4 (CX13 ∷ CCZ124 ∷ []) (CCZ124 ∷ CX13 ∷ []) tt tt Eq.refl) ▸
       at 1 2 [] (lw0 c4 (CCZ124 ∷ CCZ124 ∷ []) [] tt tt Eq.refl) ▸
       at 4 5 (Sb0-1-32-4 ∷ []) (refl) ▸
       at 4 2 (CS01 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS10-at2332 c4) ▸
       at 5 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 5 (CCZ013 ∷ []) (lw4 c4 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CCZ013 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ013-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ013-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 1 2 (CCZ013 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ013 c4) ▸
       at 0 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | TOFF012: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF012 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF012 c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ Toff012 ∷ []) (Toff012 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 1 1 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (lw4 c4 (Toff012 ∷ []) (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (K0 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at2332 c4) ▸
       at 1 2 (CCZ012 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ013-at2332 c4) ▸
       at 2 2 (K0⁻ ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd0-at2332 c4) ▸
       at 3 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 3 (Toff012 ∷ []) (lw4 c4 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (Toff012 ∷ []) tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CS42: 9 steps
lem-auto-BOX⟨0·1234⟩-∣-CS42 : Complete 4 → ⟪ (Bx0-1234 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS42 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-1234 ∷ CS24 ∷ []) (CS24 ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (CS24 ∷ []) (lw0 c4 (CS24 ∷ []) (CS24 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 0 1 (Bx0-2143 ∷ []) (lem-sym34-at1221 c4) ▸
       at 0 1 (Bx0-2413 ∷ []) (lem-sym23-at12213443 c4) ▸
       at 0 2 (CS24 ∷ Bx0-2413 ∷ []) (sym (lem-CS12-beta-at12243143 c4)) ▸
       at 1 1 (Bx0-2143 ∷ []) (lem-sym23-at12243143 c4) ▸
       at 1 1 (Bx0-2134 ∷ []) (lem-sym34-at12213443 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸ done

  b1 : Chain (CS24 ∷ Bx0-1234 ∷ []) (CS24 ∷ Bx0-1234 ∷ [])
  b1 = at 0 1 (CS24 ∷ []) (lw0 c4 (CS24 ∷ []) (CS24 ∷ []) tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CS42: 9 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS42 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS42 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-23-4 ∷ CS24 ∷ []) (CS24 ∷ Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 1 (CS14⁻ ∷ []) (refl) ▸
       at 4 2 (CS24 ∷ CS14⁻ ∷ []) (lw0 c4 (CS14⁻ ∷ CS24 ∷ []) (CS24 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 2 1 (CS14 ∷ []) (refl) ▸
       at 1 4 (CS24 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ []) (lw0 c4 (Toff423 ∷ CS14 ∷ Toff423 ∷ CS24 ∷ []) (CS24 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb0-1-4-3 ∷ []) (refl) ▸
       at 0 2 (CS24 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS42 c4) ▸ done

  b1 : Chain (CS24 ∷ Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (CS24 ∷ Sb0-1-23-4 ∷ [])
  b1 = at 1 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- auto BOX(0;1234) | CS02: 1 steps
lem-auto-BOX⟨0·1234⟩-∣-CS02 : Complete 4 → ⟪ (Bx0-1234 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS02 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CS02 ∷ []) (CS02 ∷ Bx0-1234 ∷ [])
  b0 = at 0 2 (CS02 ∷ Bx0-1234 ∷ []) (sym (lem-CS20-beta-c c4)) ▸ done


-- auto SBOX(0;1;23;4) | CS02: 11 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS02 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS02 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-23-4 ∷ CS02 ∷ []) (Bx0-1234 ∷ Toff423 ∷ CS02 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 1 (CS14⁻ ∷ []) (refl) ▸
       at 4 2 (CS02 ∷ CS14⁻ ∷ []) (pw3 c4 (CS14⁻ ∷ CS02 ∷ []) (CS02 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 3 2 (CS02 ∷ Toff423 ∷ []) (pw1 c4 (Toff423 ∷ CS02 ∷ []) (CS02 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CS14 ∷ []) (refl) ▸
       at 2 2 (CS02 ∷ CS14 ∷ []) (pw3 c4 (CS14 ∷ CS02 ∷ []) (CS02 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb0-1-4-3 ∷ []) (refl) ▸ done

  b1 : Chain (Bx0-1234 ∷ Toff423 ∷ CS02 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (CS02 ∷ Sb0-1-23-4 ∷ [])
  b1 = at 1 2 (CS02 ∷ Toff423 ∷ []) (pw1 c4 (Toff423 ∷ CS02 ∷ []) (CS02 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (CS02 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS02 c4) ▸
       at 1 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- auto BOX(0;1234) | CS01: 3 steps
lem-auto-BOX⟨0·1234⟩-∣-CS01 : Complete 4 → ⟪ (Bx0-1234 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS01 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CS01 ∷ []) (CS01 ∷ Bx0-1234 ∷ [])
  b0 = at 0 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 0 2 (CS01 ∷ Bx0-2134 ∷ []) (sym (lem-CS20-beta-c-at1221 c4)) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸ done


-- auto SBOX(0;1;23;4) | CS01: 11 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS01 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS01 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-23-4 ∷ CS01 ∷ []) (Bx0-1234 ∷ Toff423 ∷ CS01 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 1 (CS14⁻ ∷ []) (refl) ▸
       at 4 2 (CS01 ∷ CS14⁻ ∷ []) (pw2 c4 (CS14⁻ ∷ CS01 ∷ []) (CS01 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 3 2 (CS01 ∷ Toff423 ∷ []) (lem-auto-TOFF012-∣-CS34-at0412233041 c4) ▸
       at 2 1 (CS14 ∷ []) (refl) ▸
       at 2 2 (CS01 ∷ CS14 ∷ []) (pw2 c4 (CS14 ∷ CS01 ∷ []) (CS01 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb0-1-4-3 ∷ []) (refl) ▸ done

  b1 : Chain (Bx0-1234 ∷ Toff423 ∷ CS01 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (CS01 ∷ Sb0-1-23-4 ∷ [])
  b1 = at 1 2 (CS01 ∷ Toff423 ∷ []) (lem-auto-TOFF012-∣-CS34-at0412233041 c4) ▸
       at 0 2 (CS01 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS01 c4) ▸
       at 1 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- auto SBOX(0;1;23;4) | CS14: 9 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS14 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS14 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-23-4 ∷ CS14 ∷ []) (CS14 ∷ Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 1 (CS14⁻ ∷ []) (refl) ▸
       at 4 2 (CS14 ∷ CS14⁻ ∷ []) (lw0 c4 (CS14⁻ ∷ CS14 ∷ []) (CS14 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 2 1 (CS14 ∷ []) (refl) ▸
       at 1 4 (CS14 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ []) (lw0 c4 (Toff423 ∷ CS14 ∷ Toff423 ∷ CS14 ∷ []) (CS14 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb0-1-4-3 ∷ []) (refl) ▸
       at 0 2 (CS14 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14 c4) ▸ done

  b1 : Chain (CS14 ∷ Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (CS14 ∷ Sb0-1-23-4 ∷ [])
  b1 = at 1 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- auto SBOX(0;1;23;4) | CCZ023: 44 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ023 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ023 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (run b5)))))
  where
  b0 : Chain (Sb0-1-23-4 ∷ CCZ023 ∷ []) (CS03 ∷ Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ CX23 ∷ CS14⁻ ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ [])
  b0 = at 1 1 (CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ []) (lw4 c4 (CCZ023 ∷ []) (CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS03 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS20-at2332 c4) ▸
       at 1 1 (Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ []) (refl) ▸
       at 5 1 (CS14⁻ ∷ []) (refl) ▸
       at 5 2 (CX23 ∷ CS14⁻ ∷ []) (lw0 c4 (CS14⁻ ∷ CX23 ∷ []) (CX23 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sb⁻0-1-4-2 ∷ []) (refl) ▸
       at 6 1 (CS14⁻ ∷ []) (refl) ▸ done

  b1 : Chain (CS03 ∷ Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ CX23 ∷ CS14⁻ ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ []) (CS03 ∷ Bx0-1324 ∷ Toff423 ∷ CX23 ∷ CS14 ∷ CS03⁻ ∷ CX23 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS02 ∷ [])
  b1 = at 6 2 (CS03⁻ ∷ CS14⁻ ∷ []) (pw2 c4 (CS14⁻ ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Sb⁻0-1-4-2 ∷ []) (refl) ▸
       at 7 1 (CS14⁻ ∷ []) (refl) ▸
       at 7 2 (CX23 ∷ CS14⁻ ∷ []) (lw0 c4 (CS14⁻ ∷ CX23 ∷ []) (CX23 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 8 1 (Sb⁻0-1-4-2 ∷ []) (refl) ▸
       at 4 4 (CX23 ∷ CS03⁻ ∷ CX23 ∷ Toff423 ∷ []) (pw1 c4 (Toff423 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ []) (CX23 ∷ CS03⁻ ∷ CX23 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CS14 ∷ []) (refl) ▸
       at 3 2 (CX23 ∷ CS14 ∷ []) (lw0 c4 (CS14 ∷ CX23 ∷ []) (CX23 ∷ CS14 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (CS03 ∷ Bx0-1324 ∷ Toff423 ∷ CX23 ∷ CS14 ∷ CS03⁻ ∷ CX23 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS02 ∷ []) (CS03 ∷ Bx0-1324 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS02 ∷ [])
  b2 = at 4 1 (Sb0-1-4-2 ∷ []) (refl) ▸
       at 4 1 (CS14 ∷ []) (refl) ▸
       at 4 2 (CS03⁻ ∷ CS14 ∷ []) (pw2 c4 (CS14 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Sb0-1-4-2 ∷ []) (refl) ▸
       at 5 1 (CS14 ∷ []) (refl) ▸
       at 5 2 (CX23 ∷ CS14 ∷ []) (lw0 c4 (CS14 ∷ CX23 ∷ []) (CX23 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sb0-1-4-2 ∷ []) (refl) ▸
       at 2 4 (CX23 ∷ CS03⁻ ∷ CX23 ∷ Toff423 ∷ []) (pw1 c4 (Toff423 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ []) (CX23 ∷ CS03⁻ ∷ CX23 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸ done

  b3 : Chain (CS03 ∷ Bx0-1324 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS02 ∷ []) (CS03 ∷ CX23 ∷ CCZ124 ∷ CS03⁻ ∷ CX23 ∷ CX23 ∷ Bx0-1234 ∷ CX23 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS02 ∷ [])
  b3 = at 1 0 (CX23 ∷ CX23 ∷ []) (lw4 c4 [] (CX23 ∷ CX23 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸
       at 2 3 (Bx0-1234 ∷ CCZ124 ∷ []) (lem-CX23-beta c4) ▸
       at 2 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 2 2 (CCZ124 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at2332 c4) ▸
       at 3 2 (CS03⁻ ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd20-at2332 c4) ▸
       at 4 0 (CX23 ∷ CX23 ∷ []) (lw4 c4 [] (CX23 ∷ CX23 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸ done

  b4 : Chain (CS03 ∷ CX23 ∷ CCZ124 ∷ CS03⁻ ∷ CX23 ∷ CX23 ∷ Bx0-1234 ∷ CX23 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS02 ∷ []) (CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS02 ∷ [])
  b4 = at 5 3 (Bx0-1234 ∷ CCZ124 ∷ []) (lem-CX23-beta c4) ▸
       at 5 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 5 2 (CCZ124 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at2332 c4) ▸
       at 1 2 (CCZ124 ∷ CX23 ∷ []) (lw0 c4 (CX23 ∷ CCZ124 ∷ []) (CCZ124 ∷ CX23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ124 ∷ CX23 ∷ []) (lw0 c4 (CX23 ∷ CCZ124 ∷ []) (CCZ124 ∷ CX23 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ124 ∷ CS03⁻ ∷ []) (lem-comm-CSd03-CCZ124 c4) ▸
       at 2 2 (CCZ124 ∷ CX23 ∷ []) (lw0 c4 (CX23 ∷ CCZ124 ∷ []) (CCZ124 ∷ CX23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 [] (lw0 c4 (CCZ124 ∷ CCZ124 ∷ []) [] tt tt Eq.refl) ▸ done

  b5 : Chain (CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS02 ∷ []) (CCZ023 ∷ Sb0-1-23-4 ∷ [])
  b5 = at 4 5 (Sb0-1-32-4 ∷ []) (refl) ▸
       at 4 2 (CS02 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS30-at2332 c4) ▸
       at 5 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 5 (CCZ023 ∷ []) (lw4 c4 (CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CCZ023 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ023-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ023-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (CCZ023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ023 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ023 c4) ▸
       at 0 2 (CCZ023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | TOFF032: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF032 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF032 c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ Toff023 ∷ []) (Toff023 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 1 1 (K0 ∷ CCZ023 ∷ K0⁻ ∷ []) (lw4 c4 (Toff023 ∷ []) (K0 ∷ CCZ023 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (K0 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at2332 c4) ▸
       at 1 2 (CCZ023 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ023-at2332 c4) ▸
       at 2 2 (K0⁻ ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd0-at2332 c4) ▸
       at 3 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 3 (Toff023 ∷ []) (lw4 c4 (K0 ∷ CCZ023 ∷ K0⁻ ∷ []) (Toff023 ∷ []) tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CCZ032: 40 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ032 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ032 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (run b4))))
  where
  b0 : Chain (Sb0-1-23-4 ∷ CCZ023 ∷ []) (CS02 ∷ Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ CX32 ∷ CS14⁻ ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ [])
  b0 = at 1 1 (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ []) (lw4 c4 (CCZ023 ∷ []) (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS02 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS30-at2332 c4) ▸
       at 1 1 (Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ []) (refl) ▸
       at 5 1 (CS14⁻ ∷ []) (refl) ▸
       at 5 2 (CX32 ∷ CS14⁻ ∷ []) (lw0 c4 (CS14⁻ ∷ CX32 ∷ []) (CX32 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sb⁻0-1-4-2 ∷ []) (refl) ▸
       at 6 1 (CS14⁻ ∷ []) (refl) ▸ done

  b1 : Chain (CS02 ∷ Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ CX32 ∷ CS14⁻ ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ []) (CS02 ∷ Bx0-1324 ∷ Toff423 ∷ CX32 ∷ CS14 ∷ CS02⁻ ∷ CX32 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS03 ∷ [])
  b1 = at 6 2 (CS02⁻ ∷ CS14⁻ ∷ []) (pw3 c4 (CS14⁻ ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Sb⁻0-1-4-2 ∷ []) (refl) ▸
       at 7 1 (CS14⁻ ∷ []) (refl) ▸
       at 7 2 (CX32 ∷ CS14⁻ ∷ []) (lw0 c4 (CS14⁻ ∷ CX32 ∷ []) (CX32 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 8 1 (Sb⁻0-1-4-2 ∷ []) (refl) ▸
       at 4 4 (CX32 ∷ CS02⁻ ∷ CX32 ∷ Toff423 ∷ []) (pw1 c4 (Toff423 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ []) (CX32 ∷ CS02⁻ ∷ CX32 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CS14 ∷ []) (refl) ▸
       at 3 2 (CX32 ∷ CS14 ∷ []) (lw0 c4 (CS14 ∷ CX32 ∷ []) (CX32 ∷ CS14 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (CS02 ∷ Bx0-1324 ∷ Toff423 ∷ CX32 ∷ CS14 ∷ CS02⁻ ∷ CX32 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS03 ∷ []) (CS02 ∷ Bx0-1324 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS03 ∷ [])
  b2 = at 4 1 (Sb0-1-4-2 ∷ []) (refl) ▸
       at 4 1 (CS14 ∷ []) (refl) ▸
       at 4 2 (CS02⁻ ∷ CS14 ∷ []) (pw3 c4 (CS14 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Sb0-1-4-2 ∷ []) (refl) ▸
       at 5 1 (CS14 ∷ []) (refl) ▸
       at 5 2 (CX32 ∷ CS14 ∷ []) (lw0 c4 (CS14 ∷ CX32 ∷ []) (CX32 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sb0-1-4-2 ∷ []) (refl) ▸
       at 2 4 (CX32 ∷ CS02⁻ ∷ CX32 ∷ Toff423 ∷ []) (pw1 c4 (Toff423 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ []) (CX32 ∷ CS02⁻ ∷ CX32 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸ done

  b3 : Chain (CS02 ∷ Bx0-1324 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS03 ∷ []) (CS02 ∷ CCZ134 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CCZ134 ∷ Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS03 ∷ [])
  b3 = at 1 0 (CX32 ∷ CX32 ∷ []) (lw4 c4 [] (CX32 ∷ CX32 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (Bx0-1324 ∷ CCZ134 ∷ []) (lem-CX23-beta-at2332 c4) ▸
       at 2 2 (CCZ134 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at2332 c4) ▸
       at 3 2 (CS02⁻ ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd30-at2332 c4) ▸
       at 4 0 (CX32 ∷ CX32 ∷ []) (lw4 c4 [] (CX32 ∷ CX32 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (Bx0-1324 ∷ CCZ134 ∷ []) (lem-CX23-beta-at2332 c4) ▸
       at 5 2 (CCZ134 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at2332 c4) ▸
       at 1 2 (CCZ134 ∷ CX32 ∷ []) (lw0 c4 (CX32 ∷ CCZ134 ∷ []) (CCZ134 ∷ CX32 ∷ []) tt tt Eq.refl) ▸ done

  b4 : Chain (CS02 ∷ CCZ134 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CCZ134 ∷ Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS03 ∷ []) (CCZ023 ∷ Sb0-1-23-4 ∷ [])
  b4 = at 4 2 (CCZ134 ∷ CX32 ∷ []) (lw0 c4 (CX32 ∷ CCZ134 ∷ []) (CCZ134 ∷ CX32 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ134 ∷ CS02⁻ ∷ []) (lem-comm-CSd02-CCZ134 c4) ▸
       at 2 2 (CCZ134 ∷ CX32 ∷ []) (lw0 c4 (CX32 ∷ CCZ134 ∷ []) (CCZ134 ∷ CX32 ∷ []) tt tt Eq.refl) ▸
       at 1 2 [] (lw0 c4 (CCZ134 ∷ CCZ134 ∷ []) [] tt tt Eq.refl) ▸
       at 4 5 (Sb0-1-32-4 ∷ []) (refl) ▸
       at 4 2 (CS03 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS20-at2332 c4) ▸
       at 5 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 5 (CCZ023 ∷ []) (lw4 c4 (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(0;1432) @2332: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩-at2332 : Complete 4 → ⟪ (Sb⁻0-1-3-2 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ Sb⁻0-1-3-2 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-3-2 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ Sb⁻0-1-3-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·3·2⟩ c4) ▸
       at 2 2 (Bx0-1432 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1423⟩ c4) ▸
       at 1 2 (Bx0-1432 ∷ Sb⁻0-1-2-3 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩ c4) ▸
       at 0 2 (Bx0-1423 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1432⟩ c4) ▸
       at 1 2 (Sb⁻0-1-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·2·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(0;1432) @243243: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩-at243243 : Complete 4 → ⟪ (Sb⁻0-1-4-2 ∷ Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ Sb⁻0-1-4-2 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-4-2 ∷ Bx0-1324 ∷ []) (Bx0-1324 ∷ Sb⁻0-1-4-2 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-3-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·4·2⟩ c4) ▸
       at 2 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ c4) ▸
       at 1 2 (Bx0-1423 ∷ Sb⁻0-1-3-2 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩-at2332 c4) ▸
       at 0 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ c4) ▸
       at 1 2 (Sb⁻0-1-4-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·3·2⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(0;1432) @2442: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩-at2442 : Complete 4 → ⟪ (Sb⁻0-1-4-3 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ Sb⁻0-1-4-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩-at2442 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-4-3 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·4·3⟩ c4) ▸
       at 2 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ c4) ▸
       at 1 2 (Bx0-1324 ∷ Sb⁻0-1-4-2 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩-at243243 c4) ▸
       at 0 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ c4) ▸
       at 1 2 (Sb⁻0-1-4-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·4·2⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;2;3) | BOX(0;1432) @2332: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩-at2332 : Complete 4 → ⟪ (Sb0-1-3-2 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ Sb0-1-3-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-3-2 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ Sb0-1-3-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·3·2⟩ c4) ▸
       at 2 2 (Bx0-1432 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1423⟩ c4) ▸
       at 1 2 (Bx0-1432 ∷ Sb0-1-2-3 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩ c4) ▸
       at 0 2 (Bx0-1423 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1432⟩ c4) ▸
       at 1 2 (Sb0-1-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·2·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;2;3) | BOX(0;1432) @243243: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩-at243243 : Complete 4 → ⟪ (Sb0-1-4-2 ∷ Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ Sb0-1-4-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-4-2 ∷ Bx0-1324 ∷ []) (Bx0-1324 ∷ Sb0-1-4-2 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-3-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·4·2⟩ c4) ▸
       at 2 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ c4) ▸
       at 1 2 (Bx0-1423 ∷ Sb0-1-3-2 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩-at2332 c4) ▸
       at 0 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ c4) ▸
       at 1 2 (Sb0-1-4-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·3·2⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;2;3) | BOX(0;1432) @2442: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩-at2442 : Complete 4 → ⟪ (Sb0-1-4-3 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ Sb0-1-4-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩-at2442 c4 = run b0
  where
  b0 : Chain (Sb0-1-4-3 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ Sb0-1-4-3 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·4·3⟩ c4) ▸
       at 2 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ c4) ▸
       at 1 2 (Bx0-1324 ∷ Sb0-1-4-2 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩-at243243 c4) ▸
       at 0 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ c4) ▸
       at 1 2 (Sb0-1-4-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·4·2⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | BOX(0;1234): 30 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·1234⟩ : Complete 4 → ⟪ (Sb0-1-23-4 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·1234⟩ c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Sb0-1-23-4 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Bx0-2314 ∷ CCZ123 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 2 (Bx0-1234 ∷ Sb⁻0-1-4-3 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩-at2442 c4) ▸
       at 5 0 (Toff423 ∷ Toff423 ∷ []) (lw0 c4 [] (Toff423 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 4 1 (Bx0-2314 ∷ []) (lem-sym23-at1221 c4) ▸
       at 4 1 (Bx0-2341 ∷ []) (lem-sym34-at122331 c4) ▸
       at 3 3 (Bx0-2341 ∷ CCZ123 ∷ []) (lem-T312-beta-at12233441 c4) ▸
       at 3 1 (Bx0-2314 ∷ []) (lem-sym34-at12233441 c4) ▸ done

  b1 : Chain (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Bx0-2314 ∷ CCZ123 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (Bx0-1234 ∷ Bx0-2341 ∷ CCZ123 ∷ Toff423 ∷ Sb0-1-4-3 ∷ CCZ123 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b1 = at 3 1 (Bx0-2134 ∷ []) (lem-sym23-at122331 c4) ▸
       at 3 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸
       at 2 2 (Bx0-1234 ∷ Sb0-1-4-3 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩-at2442 c4) ▸
       at 3 0 (Toff423 ∷ Toff423 ∷ []) (lw0 c4 [] (Toff423 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
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
       at 5 3 (Toff423 ∷ CS14⁻ ∷ CCZ123 ∷ []) (lw0 c4 (CCZ123 ∷ Toff423 ∷ CS14⁻ ∷ []) (Toff423 ∷ CS14⁻ ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 1 (CS14 ∷ []) (refl) ▸ done

  b3 : Chain (Bx0-1234 ∷ Bx0-1234 ∷ CCZ123 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ CCZ123 ∷ []) (Bx0-1234 ∷ Sb0-1-23-4 ∷ [])
  b3 = at 6 1 (CS14⁻ ∷ []) (refl) ▸
       at 2 5 (Toff423 ∷ CS14 ∷ Toff423 ∷ CS14⁻ ∷ CCZ123 ∷ []) (lw0 c4 (CCZ123 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ CS14⁻ ∷ []) (Toff423 ∷ CS14 ∷ Toff423 ∷ CS14⁻ ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb0-1-4-3 ∷ []) (refl) ▸
       at 5 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 6 2 [] (lw4 c4 (CCZ123 ∷ CCZ123 ∷ []) [] tt tt Eq.refl) ▸
       at 1 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- auto CCZ012 | SBOX(3;0;14;2): 9 steps
lem-auto-CCZ012-∣-SBOX⟨3·0·14·2⟩ : Complete 4 → ⟪ (CCZ012 ∷ Sb3-0-14-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-14-2 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·0·14·2⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ012 ∷ Sb3-0-14-2 ∷ []) (Bx3-0142 ∷ Toff214 ∷ Sb3-0-2-4 ∷ Toff214 ∷ Sb⁻3-0-2-4 ∷ CCZ012 ∷ [])
  b0 = at 1 1 (Bx3-0142 ∷ Toff214 ∷ Sb3-0-2-4 ∷ Toff214 ∷ Sb⁻3-0-2-4 ∷ []) (refl) ▸
       at 0 2 (Bx3-0142 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0142⟩ c4) ▸
       at 3 1 (CS02 ∷ []) (refl) ▸
       at 1 4 (Toff214 ∷ CS02 ∷ Toff214 ∷ CCZ012 ∷ []) (pw3 c4 (CCZ012 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ []) (Toff214 ∷ CS02 ∷ Toff214 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb3-0-2-4 ∷ []) (refl) ▸
       at 5 1 (CS02⁻ ∷ []) (refl) ▸
       at 4 2 (CS02⁻ ∷ CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻3-0-2-4 ∷ []) (refl) ▸ done

  b1 : Chain (Bx3-0142 ∷ Toff214 ∷ Sb3-0-2-4 ∷ Toff214 ∷ Sb⁻3-0-2-4 ∷ CCZ012 ∷ []) (Sb3-0-14-2 ∷ CCZ012 ∷ [])
  b1 = at 0 5 (Sb3-0-14-2 ∷ []) (refl) ▸ done


-- auto SBOX(0;1;23;4) | CS14 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS14-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS14-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CS14 ∷ []) (CS14 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (CS14 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS14 ∷ []) (CS14 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS14 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS14 c4) ▸
       at 0 2 (CS14 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS14 ∷ []) (CS14 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOX(0;1;4;3): 5 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩ : Complete 4 → ⟪ (Sb0-1-23-4 ∷ Sb0-1-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-4-3 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩ c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ Sb0-1-4-3 ∷ []) (Sb0-1-4-3 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 1 1 (CS14 ∷ []) (refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS14 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS14-at2332 c4) ▸
       at 1 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 1 (Sb0-1-4-3 ∷ []) (refl) ▸ done


-- auto SBOX(0;1;23;4) | CSd14: 9 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd14 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd14 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-23-4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 1 (CS14⁻ ∷ []) (refl) ▸
       at 4 2 (CS14⁻ ∷ CS14⁻ ∷ []) (lw0 c4 (CS14⁻ ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 2 1 (CS14 ∷ []) (refl) ▸
       at 1 4 (CS14⁻ ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ []) (lw0 c4 (Toff423 ∷ CS14 ∷ Toff423 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb0-1-4-3 ∷ []) (refl) ▸
       at 0 2 (CS14⁻ ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14 c4) ▸ done

  b1 : Chain (CS14⁻ ∷ Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (CS14⁻ ∷ Sb0-1-23-4 ∷ [])
  b1 = at 1 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- auto SBOX(0;1;23;4) | CSd14 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd14-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd14-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (CS14⁻ ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS14⁻ ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd14 c4) ▸
       at 0 2 (CS14⁻ ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOXd(0;1;4;3): 5 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩ : Complete 4 → ⟪ (Sb0-1-23-4 ∷ Sb⁻0-1-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-4-3 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩ c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ Sb⁻0-1-4-3 ∷ []) (Sb⁻0-1-4-3 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 1 1 (CS14⁻ ∷ []) (refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS14⁻ ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd14-at2332 c4) ▸
       at 1 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸ done


-- sym12 @01132032: 5 steps
lem-sym12-at01132032 : Complete 4 → ⟪ (Bx1-3024 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0324 ∷ []) ⟫ʷ
lem-sym12-at01132032 c4 = run b0
  where
  b0 : Chain (Bx1-3024 ∷ []) (Bx1-0324 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-3124 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·3024⟩ c4) ▸
       at 1 1 (Bx0-1324 ∷ []) (lem-sym12-at132132 c4) ▸
       at 0 2 (Bx1-0324 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1324⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym12 @02132031: 5 steps
lem-sym12-at02132031 : Complete 4 → ⟪ (Bx2-3014 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0314 ∷ []) ⟫ʷ
lem-sym12-at02132031 c4 = run b0
  where
  b0 : Chain (Bx2-3014 ∷ []) (Bx2-0314 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-3024 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·3014⟩ c4) ▸
       at 1 1 (Bx1-0324 ∷ []) (lem-sym12-at01132032 c4) ▸
       at 0 2 (Bx2-0314 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0324⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym12 @02132130: 5 steps
lem-sym12-at02132130 : Complete 4 → ⟪ (Bx2-3104 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1304 ∷ []) ⟫ʷ
lem-sym12-at02132130 c4 = run b0
  where
  b0 : Chain (Bx2-3104 ∷ []) (Bx2-1304 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-3014 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·3104⟩ c4) ▸
       at 1 1 (Bx2-0314 ∷ []) (lem-sym12-at02132031 c4) ▸
       at 0 2 (Bx2-1304 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·0314⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @022330: 5 steps
lem-sym23-at022330 : Complete 4 → ⟪ (Bx2-1304 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1034 ∷ []) ⟫ʷ
lem-sym23-at022330 c4 = run b0
  where
  b0 : Chain (Bx2-1304 ∷ []) (Bx2-1034 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-0314 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1304⟩ c4) ▸
       at 1 1 (Bx2-0134 ∷ []) (lem-sym23-at02102331 c4) ▸
       at 0 2 (Bx2-1034 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·0134⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- CSd12-beta @0110: 7 steps
lem-CSd12-beta-at0110 : Complete 4 → ⟪ (CS02⁻ ∷ Bx1-0234 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0234 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-CSd12-beta-at0110 c4 = run b0
  where
  b0 : Chain (CS02⁻ ∷ Bx1-0234 ∷ []) (Bx1-0234 ∷ CS02⁻ ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS12⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS02⁻ ∷ []) (CS12⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-1234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0234⟩ c4) ▸
       at 1 2 (Bx0-1234 ∷ CS12⁻ ∷ []) (lem-CSd12-beta c4) ▸
       at 0 2 (Bx1-0234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1234⟩ c4) ▸
       at 1 2 (CS02⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS12⁻ ∷ []) (CS02⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- CSd12-beta @021021: 7 steps
lem-CSd12-beta-at021021 : Complete 4 → ⟪ (CS01⁻ ∷ Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ CS01⁻ ∷ []) ⟫ʷ
lem-CSd12-beta-at021021 c4 = run b0
  where
  b0 : Chain (CS01⁻ ∷ Bx2-0134 ∷ []) (Bx2-0134 ∷ CS01⁻ ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS02⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd01 c4) ▸
       at 2 2 (Bx1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0134⟩ c4) ▸
       at 1 2 (Bx1-0234 ∷ CS02⁻ ∷ []) (lem-CSd12-beta-at0110 c4) ▸
       at 0 2 (Bx2-0134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0234⟩ c4) ▸
       at 1 2 (CS01⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd02 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- CSd12-beta @0220: 7 steps
lem-CSd12-beta-at0220 : Complete 4 → ⟪ (CS01⁻ ∷ Bx2-1034 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1034 ∷ CS01⁻ ∷ []) ⟫ʷ
lem-CSd12-beta-at0220 c4 = run b0
  where
  b0 : Chain (CS01⁻ ∷ Bx2-1034 ∷ []) (Bx2-1034 ∷ CS01⁻ ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS01⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx2-0134 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1034⟩ c4) ▸
       at 1 2 (Bx2-0134 ∷ CS01⁻ ∷ []) (lem-CSd12-beta-at021021 c4) ▸
       at 0 2 (Bx2-1034 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·0134⟩ c4) ▸
       at 1 2 (CS01⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @0220: 5 steps
lem-sym23-at0220 : Complete 4 → ⟪ (Bx2-1034 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1304 ∷ []) ⟫ʷ
lem-sym23-at0220 c4 = run b0
  where
  b0 : Chain (Bx2-1034 ∷ []) (Bx2-1304 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-0134 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1034⟩ c4) ▸
       at 1 1 (Bx2-0314 ∷ []) (lem-sym23-at021021 c4) ▸
       at 0 2 (Bx2-1304 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·0314⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym12 @01102332: 5 steps
lem-sym12-at01102332 : Complete 4 → ⟪ (Bx1-0324 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3024 ∷ []) ⟫ʷ
lem-sym12-at01102332 c4 = run b0
  where
  b0 : Chain (Bx1-0324 ∷ []) (Bx1-3024 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1324 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0324⟩ c4) ▸
       at 1 1 (Bx0-3124 ∷ []) (lem-sym12-at2332 c4) ▸
       at 0 2 (Bx1-3024 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·3124⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym12 @02102331: 5 steps
lem-sym12-at02102331 : Complete 4 → ⟪ (Bx2-0314 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3014 ∷ []) ⟫ʷ
lem-sym12-at02102331 c4 = run b0
  where
  b0 : Chain (Bx2-0314 ∷ []) (Bx2-3014 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0324 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0314⟩ c4) ▸
       at 1 1 (Bx1-3024 ∷ []) (lem-sym12-at01102332 c4) ▸
       at 0 2 (Bx2-3014 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·3024⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym12 @022330: 5 steps
lem-sym12-at022330 : Complete 4 → ⟪ (Bx2-1304 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3104 ∷ []) ⟫ʷ
lem-sym12-at022330 c4 = run b0
  where
  b0 : Chain (Bx2-1304 ∷ []) (Bx2-3104 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-0314 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1304⟩ c4) ▸
       at 1 1 (Bx2-3014 ∷ []) (lem-sym12-at02102331 c4) ▸
       at 0 2 (Bx2-3104 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·3014⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CSd01 | BOX(2;3104): 7 steps
lem-auto-CSd01-∣-BOX⟨2·3104⟩ : Complete 4 → ⟪ (CS01⁻ ∷ Bx2-3104 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3104 ∷ CS01⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨2·3104⟩ c4 = run b0
  where
  b0 : Chain (CS01⁻ ∷ Bx2-3104 ∷ []) (Bx2-3104 ∷ CS01⁻ ∷ [])
  b0 = at 0 1 (CS01⁻ ∷ []) (lw4 c4 (CS01⁻ ∷ []) (CS01⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx2-1304 ∷ []) (lem-sym12-at02132130 c4) ▸
       at 1 1 (Bx2-1034 ∷ []) (lem-sym23-at022330 c4) ▸
       at 0 2 (Bx2-1034 ∷ CS01⁻ ∷ []) (lem-CSd12-beta-at0220 c4) ▸
       at 0 1 (Bx2-1304 ∷ []) (lem-sym23-at0220 c4) ▸
       at 0 1 (Bx2-3104 ∷ []) (lem-sym12-at022330 c4) ▸
       at 1 1 (CS01⁻ ∷ []) (lw4 c4 (CS01⁻ ∷ []) (CS01⁻ ∷ []) tt tt Eq.refl) ▸ done


-- beta-T @01122330: 8 steps
lem-beta-T-at01122330 : Complete 4 → ⟪ (Bx1-2304 ∷ []) ⟫ʷ ≈ ⟪ (Toff123 ∷ CCZ014 ∷ Toff123 ∷ CCZ014 ∷ []) ⟫ʷ
lem-beta-T-at01122330 c4 = run b0
  where
  b0 : Chain (Bx1-2304 ∷ []) (Toff123 ∷ CCZ014 ∷ Toff123 ∷ CCZ014 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-2314 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2304⟩ c4) ▸
       at 1 1 (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) (lem-beta-T-at122331 c4) ▸
       at 0 2 (Toff123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff023 ∷ []) (Toff123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 2 2 (Toff123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff023 ∷ []) (Toff123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 4 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto S0 | BOX(1;2304): 6 steps
lem-auto-S0-∣-BOX⟨1·2304⟩ : Complete 4 → ⟪ (S0 ∷ Bx1-2304 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2304 ∷ S0 ∷ []) ⟫ʷ
lem-auto-S0-∣-BOX⟨1·2304⟩ c4 = run b0
  where
  b0 : Chain (S0 ∷ Bx1-2304 ∷ []) (Bx1-2304 ∷ S0 ∷ [])
  b0 = at 1 1 (Toff123 ∷ CCZ014 ∷ Toff123 ∷ CCZ014 ∷ []) (lem-beta-T-at01122330 c4) ▸
       at 0 2 (Toff123 ∷ S0 ∷ []) (c₁ (S) (Toff)) ▸
       at 1 2 (CCZ014 ∷ S0 ∷ []) (pw2 c4 (S0 ∷ CCZ014 ∷ []) (CCZ014 ∷ S0 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff123 ∷ S0 ∷ []) (c₁ (S) (Toff)) ▸
       at 3 2 (CCZ014 ∷ S0 ∷ []) (pw2 c4 (S0 ∷ CCZ014 ∷ []) (CCZ014 ∷ S0 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx1-2304 ∷ []) (sym (lem-beta-T-at01122330 c4)) ▸ done


-- auto BOX(0;1234) | CS40: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS40 : Complete 4 → ⟪ (Bx0-1234 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS40 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CS04 ∷ []) (CS04 ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (CS04 ∷ []) (pw1 c4 (CS04 ∷ []) (CS04 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx0-1243 ∷ []) (lem-sym34 c4) ▸
       at 0 1 (Bx0-1423 ∷ []) (lem-sym23-at3443 c4) ▸
       at 0 2 (CS04 ∷ Bx0-1423 ∷ []) (sym (lem-CS20-beta-c-at243243 c4)) ▸
       at 1 1 (Bx0-1243 ∷ []) (lem-sym23-at243243 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym34-at3443 c4) ▸
       at 0 1 (CS04 ∷ []) (pw1 c4 (CS04 ∷ []) (CS04 ∷ []) tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CSd40: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd40 : Complete 4 → ⟪ (Bx0-1234 ∷ CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS04⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd40 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (CS04⁻ ∷ []) (pw1 c4 (CS04⁻ ∷ []) (CS04⁻ ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx0-1243 ∷ []) (lem-sym34 c4) ▸
       at 0 1 (Bx0-1423 ∷ []) (lem-sym23-at3443 c4) ▸
       at 0 2 (CS04⁻ ∷ Bx0-1423 ∷ []) (sym (lem-CS20-beta-ci-at243243 c4)) ▸
       at 1 1 (Bx0-1243 ∷ []) (lem-sym23-at243243 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym34-at3443 c4) ▸
       at 0 1 (CS04⁻ ∷ []) (pw1 c4 (CS04⁻ ∷ []) (CS04⁻ ∷ []) tt tt Eq.refl) ▸ done


-- beta-T @011220: 8 steps
lem-beta-T-at011220 : Complete 4 → ⟪ (Bx1-2034 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CCZ134 ∷ Toff102 ∷ CCZ134 ∷ []) ⟫ʷ
lem-beta-T-at011220 c4 = run b0
  where
  b0 : Chain (Bx1-2034 ∷ []) (Toff102 ∷ CCZ134 ∷ Toff102 ∷ CCZ134 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-2134 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2034⟩ c4) ▸
       at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-beta-T-at1221 c4) ▸
       at 0 2 (Toff102 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff012 ∷ []) (Toff102 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 2 2 (Toff102 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff012 ∷ []) (Toff102 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 4 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto Sd0 | BOX(1;2034): 6 steps
lem-auto-Sd0-∣-BOX⟨1·2034⟩ : Complete 4 → ⟪ (S0⁻ ∷ Bx1-2034 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2034 ∷ S0⁻ ∷ []) ⟫ʷ
lem-auto-Sd0-∣-BOX⟨1·2034⟩ c4 = run b0
  where
  b0 : Chain (S0⁻ ∷ Bx1-2034 ∷ []) (Bx1-2034 ∷ S0⁻ ∷ [])
  b0 = at 1 1 (Toff102 ∷ CCZ134 ∷ Toff102 ∷ CCZ134 ∷ []) (lem-beta-T-at011220 c4) ▸
       at 0 2 (Toff102 ∷ S0⁻ ∷ []) (lw4 c4 (S0⁻ ∷ Toff102 ∷ []) (Toff102 ∷ S0⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ134 ∷ S0⁻ ∷ []) (c₁ (S • S • S) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑)) ▸
       at 2 2 (Toff102 ∷ S0⁻ ∷ []) (lw4 c4 (S0⁻ ∷ Toff102 ∷ []) (Toff102 ∷ S0⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ134 ∷ S0⁻ ∷ []) (c₁ (S • S • S) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑)) ▸
       at 0 4 (Bx1-2034 ∷ []) (sym (lem-beta-T-at011220 c4)) ▸ done


-- auto Sd0 | SBOX(1;2;03;4): 11 steps
lem-auto-Sd0-∣-SBOX⟨1·2·03·4⟩ : Complete 4 → ⟪ (S0⁻ ∷ Sb1-2-03-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-03-4 ∷ S0⁻ ∷ []) ⟫ʷ
lem-auto-Sd0-∣-SBOX⟨1·2·03·4⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (S0⁻ ∷ Sb1-2-03-4 ∷ []) (Bx1-2034 ∷ Toff403 ∷ Sb1-2-4-3 ∷ Toff403 ∷ S0⁻ ∷ CS24⁻ ∷ [])
  b0 = at 1 1 (Bx1-2034 ∷ Toff403 ∷ Sb1-2-4-3 ∷ Toff403 ∷ Sb⁻1-2-4-3 ∷ []) (refl) ▸
       at 0 2 (Bx1-2034 ∷ S0⁻ ∷ []) (lem-auto-Sd0-∣-BOX⟨1·2034⟩ c4) ▸
       at 1 2 (Toff403 ∷ S0⁻ ∷ []) (pw1 c4 (S0⁻ ∷ Toff403 ∷ []) (Toff403 ∷ S0⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CS24 ∷ []) (refl) ▸
       at 2 2 (CS24 ∷ S0⁻ ∷ []) (lw1 c4 (S0⁻ ∷ CS24 ∷ []) (CS24 ∷ S0⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb1-2-4-3 ∷ []) (refl) ▸
       at 3 2 (Toff403 ∷ S0⁻ ∷ []) (pw1 c4 (S0⁻ ∷ Toff403 ∷ []) (Toff403 ∷ S0⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS24⁻ ∷ []) (refl) ▸ done

  b1 : Chain (Bx1-2034 ∷ Toff403 ∷ Sb1-2-4-3 ∷ Toff403 ∷ S0⁻ ∷ CS24⁻ ∷ []) (Sb1-2-03-4 ∷ S0⁻ ∷ [])
  b1 = at 4 2 (CS24⁻ ∷ S0⁻ ∷ []) (lw1 c4 (S0⁻ ∷ CS24⁻ ∷ []) (CS24⁻ ∷ S0⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻1-2-4-3 ∷ []) (refl) ▸
       at 0 5 (Sb1-2-03-4 ∷ []) (refl) ▸ done


-- sym34 @0112233440: 5 steps
lem-sym34-at0112233440 : Complete 4 → ⟪ (Bx1-2340 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2304 ∷ []) ⟫ʷ
lem-sym34-at0112233440 c4 = run b0
  where
  b0 : Chain (Bx1-2340 ∷ []) (Bx1-2304 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-2341 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2340⟩ c4) ▸
       at 1 1 (Bx0-2314 ∷ []) (lem-sym34-at12233441 c4) ▸
       at 0 2 (Bx1-2304 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2314⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- CS20-beta-ci @1221: 7 steps
lem-CS20-beta-ci-at1221 : Complete 4 → ⟪ (CS01⁻ ∷ Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ CS01⁻ ∷ []) ⟫ʷ
lem-CS20-beta-ci-at1221 c4 = run b0
  where
  b0 : Chain (CS01⁻ ∷ Bx0-2134 ∷ []) (Bx0-2134 ∷ CS01⁻ ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS02⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd01 c4) ▸
       at 2 2 (Bx0-1234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2134⟩ c4) ▸
       at 1 2 (Bx0-1234 ∷ CS02⁻ ∷ []) (lem-CS20-beta-ci c4) ▸
       at 0 2 (Bx0-2134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1234⟩ c4) ▸
       at 1 2 (CS01⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd02 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- CS20-beta-ci @011220: 7 steps
lem-CS20-beta-ci-at011220 : Complete 4 → ⟪ (CS01⁻ ∷ Bx1-2034 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2034 ∷ CS01⁻ ∷ []) ⟫ʷ
lem-CS20-beta-ci-at011220 c4 = run b0
  where
  b0 : Chain (CS01⁻ ∷ Bx1-2034 ∷ []) (Bx1-2034 ∷ CS01⁻ ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS01⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-2134 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2034⟩ c4) ▸
       at 1 2 (Bx0-2134 ∷ CS01⁻ ∷ []) (lem-CS20-beta-ci-at1221 c4) ▸
       at 0 2 (Bx1-2034 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2134⟩ c4) ▸
       at 1 2 (CS01⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym34 @01122330: 5 steps
lem-sym34-at01122330 : Complete 4 → ⟪ (Bx1-2304 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2340 ∷ []) ⟫ʷ
lem-sym34-at01122330 c4 = run b0
  where
  b0 : Chain (Bx1-2304 ∷ []) (Bx1-2340 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-2314 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2304⟩ c4) ▸
       at 1 1 (Bx0-2341 ∷ []) (lem-sym34-at122331 c4) ▸
       at 0 2 (Bx1-2340 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2341⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


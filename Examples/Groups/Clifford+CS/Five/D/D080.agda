{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D080 where

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
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-BOXd-BOX ; lem-Cz-beta ; lem-sym12 ; lem-sym23 ; lem-sym34)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-beta-T-at132132 ; lem-sym12-at0314203142 ; lem-sym12-at1221 ; lem-sym12-at132132 ; lem-sym23-at132132 ; lem-sym34-at1221)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-CX10-beta-c-at0110 ; lem-Cz-beta-at12243143 ; lem-c124-beta-at0310213442 ; lem-sym12-at0110 ; lem-sym12-at011220 ; lem-sym12-at233442 ; lem-sym23-at12213443 ; lem-sym23-at12243143 ; lem-sym23-at13213442 ; lem-sym23-at13243142 ; lem-sym23-at2332 ; lem-sym23-at243243 ; lem-sym23-at3443 ; lem-sym34-at12213443 ; lem-sym34-at13213442 ; lem-sym34-at2332 ; lem-sym34-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-BOXd-BOX-at2332 ; lem-CS20-beta-c-at1221 ; lem-beta-T-at0110 ; lem-sym12-at0210243143 ; lem-sym12-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-CX23-beta-at2332 ; lem-sym23-at0310213442 ; lem-sym23-at0310243142)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-F0-at14213243 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at2332 ; lem-sym34-at0210233441)
open import Examples.Groups.Clifford+CS.Five.D.D007 using (lem-CS12-beta-at021021 ; lem-SBsym-at0113203442 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CS24-at2332 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at2332 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd4-at2332 ; lem-sym12-at0210233441 ; lem-sym34-at02102331)
open import Examples.Groups.Clifford+CS.Five.D.D008 using (lem-SBsymd-at0113203442 ; lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS20-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D009 using (lem-CS20-beta-c-at2332 ; lem-CS20-beta-ci-at243243 ; lem-auto-BOX⟨0·1234⟩-∣-CSd20 ; lem-auto-BOX⟨0·1234⟩-∣-CSd30 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CS20-at2332 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CS30-at2332 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at2332 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd0-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D010 using (lem-CSd12-beta-at021021 ; lem-sym12-at02132130 ; lem-sym23-at0220 ; lem-sym23-at022330)
open import Examples.Groups.Clifford+CS.Five.D.D011 using (lem-CS20-beta-c-at011220)
open import Examples.Groups.Clifford+CS.Five.D.D079 using (lem-CSd12-beta-at13243142 ; lem-auto-BOXd⟨0·1234⟩-∣-CS43 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CS34-at2332 ; lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS30)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-CCZ024 ; lem-nat-2-BOX⟨0·1234⟩ ; lem-nat-2-BOX⟨0·1324⟩)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-2-BOX⟨2·4013⟩)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-1-TOFF013 ; lem-nat-2-CZ03)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-0-BOX⟨0·1234⟩ ; lem-nat-0-BOX⟨1·0234⟩ ; lem-nat-1-BOX⟨1·0234⟩ ; lem-nat-1-BOX⟨2·0134⟩ ; lem-nat-2-BOX⟨3·0412⟩ ; lem-nat-2-CZ02)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-2-CS02 ; lem-nat-2-SBOX⟨0·1·23·4⟩ ; lem-nat-2-SBOX⟨0·1·32·4⟩)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-0-BOX⟨2·0341⟩)
open import Examples.Groups.Clifford+CS.Five.D.R016 using (lem-nat-0-BOX⟨0·3142⟩ ; lem-nat-0-BOX⟨1·3042⟩ ; lem-nat-1-BOX⟨1·3042⟩ ; lem-nat-1-BOX⟨2·3041⟩)
open import Examples.Groups.Clifford+CS.Five.D.R018 using (lem-nat-2-SBOXd⟨0·1·23·4⟩ ; lem-nat-2-SBOXd⟨0·1·32·4⟩)
open import Examples.Groups.Clifford+CS.Five.D.R019 using (lem-nat-0-BOX⟨0·3124⟩ ; lem-nat-0-BOX⟨2·0134⟩ ; lem-nat-0-BOX⟨2·0314⟩ ; lem-nat-0-BOX⟨2·1034⟩ ; lem-nat-0-BOX⟨2·1304⟩ ; lem-nat-0-BOX⟨2·3014⟩ ; lem-nat-1-BOX⟨1·3024⟩ ; lem-nat-2-CS03)
open import Examples.Groups.Clifford+CS.Five.D.R020 using (lem-nat-2-BOX⟨1·0243⟩)
open import Examples.Groups.Clifford+CS.Five.D.R021 using (lem-nat-0-BOX⟨2·3041⟩ ; lem-nat-0-BOX⟨2·3140⟩)
open import Examples.Groups.Clifford+CS.Five.D.R025 using (lem-comm-CCZ014-CX23 ; lem-nat-0-BOX⟨0·3412⟩ ; lem-nat-0-BOX⟨1·3402⟩ ; lem-nat-0-BOX⟨2·1340⟩ ; lem-nat-0-BOX⟨2·3401⟩ ; lem-nat-0-BOX⟨2·3410⟩ ; lem-nat-1-BOX⟨0·3214⟩ ; lem-nat-1-BOX⟨1·3402⟩ ; lem-nat-1-BOX⟨2·3401⟩ ; lem-nat-1-SBOX⟨2·0·34·1⟩ ; lem-nat-3-BOX⟨1·0243⟩)
open import Examples.Groups.Clifford+CS.Five.D.R026 using (lem-nat-2-BOX⟨1·0342⟩ ; lem-nat-3-BOX⟨1·0234⟩)
-- auto SBOXd(0;1;23;4) | CS43: 9 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS43 : Complete 4 → ⟪ (Sb⁻0-1-23-4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS43 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb⁻0-1-23-4 ∷ CS34 ∷ []) (CS34 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ [])
  b0 = at 0 1 (Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) (refl) ▸
       at 4 2 (CS34 ∷ Bx⁻0-1234 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-CS43 c4) ▸
       at 2 1 (CS14⁻ ∷ []) (refl) ▸
       at 1 4 (CS34 ∷ Toff423 ∷ CS14⁻ ∷ Toff423 ∷ []) (lw0 c4 (Toff423 ∷ CS14⁻ ∷ Toff423 ∷ CS34 ∷ []) (CS34 ∷ Toff423 ∷ CS14⁻ ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 0 1 (CS14 ∷ []) (refl) ▸
       at 0 2 (CS34 ∷ CS14 ∷ []) (lw0 c4 (CS14 ∷ CS34 ∷ []) (CS34 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Sb0-1-4-3 ∷ []) (refl) ▸ done

  b1 : Chain (CS34 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) (CS34 ∷ Sb⁻0-1-23-4 ∷ [])
  b1 = at 1 5 (Sb⁻0-1-23-4 ∷ []) (refl) ▸ done


-- auto BOXd(0;1234) | CS03: 5 steps
lem-auto-BOXd⟨0·1234⟩-∣-CS03 : Complete 4 → ⟪ (Bx⁻0-1234 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Bx⁻0-1234 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CS03 c4 = run b0
  where
  b0 : Chain (Bx⁻0-1234 ∷ CS03 ∷ []) (CS03 ∷ Bx⁻0-1234 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ []) (lem-BOXd-BOX c4) ▸
       at 0 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 0 2 (CS03 ∷ Bx0-1324 ∷ []) (sym (lem-CS20-beta-c-at2332 c4)) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸
       at 1 1 (Bx⁻0-1234 ∷ []) (sym (lem-BOXd-BOX c4)) ▸ done


-- auto SBOXd(0;1;23;4) | CS03: 11 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS03 : Complete 4 → ⟪ (Sb⁻0-1-23-4 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS03 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb⁻0-1-23-4 ∷ CS03 ∷ []) (CS14 ∷ CS03 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ [])
  b0 = at 0 1 (Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) (refl) ▸
       at 4 2 (CS03 ∷ Bx⁻0-1234 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-CS03 c4) ▸
       at 3 2 (CS03 ∷ Toff423 ∷ []) (pw1 c4 (Toff423 ∷ CS03 ∷ []) (CS03 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CS14⁻ ∷ []) (refl) ▸
       at 2 2 (CS03 ∷ CS14⁻ ∷ []) (pw2 c4 (CS14⁻ ∷ CS03 ∷ []) (CS03 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 1 2 (CS03 ∷ Toff423 ∷ []) (pw1 c4 (Toff423 ∷ CS03 ∷ []) (CS03 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (CS14 ∷ []) (refl) ▸ done

  b1 : Chain (CS14 ∷ CS03 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) (CS03 ∷ Sb⁻0-1-23-4 ∷ [])
  b1 = at 0 2 (CS03 ∷ CS14 ∷ []) (pw2 c4 (CS14 ∷ CS03 ∷ []) (CS03 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Sb0-1-4-3 ∷ []) (refl) ▸
       at 1 5 (Sb⁻0-1-23-4 ∷ []) (refl) ▸ done


-- auto BOXd(0;1234) | CCZ024: 9 steps
lem-auto-BOXd⟨0·1234⟩-∣-CCZ024 : Complete 4 → ⟪ (Bx⁻0-1234 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Bx⁻0-1234 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CCZ024 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx⁻0-1234 ∷ CCZ024 ∷ []) (CCZ024 ∷ Bx0-1234 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ []) (lem-BOXd-BOX c4) ▸
       at 0 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 0 1 (Bx0-2143 ∷ []) (lem-sym34-at1221 c4) ▸
       at 0 1 (Bx0-2413 ∷ []) (lem-sym23-at12213443 c4) ▸
       at 0 2 (CCZ024 ∷ Bx0-2413 ∷ []) (sym (lem-Cz-beta-at12243143 c4)) ▸
       at 1 1 (Bx0-2143 ∷ []) (lem-sym23-at12243143 c4) ▸
       at 1 1 (Bx0-2134 ∷ []) (lem-sym34-at12213443 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸ done

  b1 : Chain (CCZ024 ∷ Bx0-1234 ∷ []) (CCZ024 ∷ Bx⁻0-1234 ∷ [])
  b1 = at 1 1 (Bx⁻0-1234 ∷ []) (sym (lem-BOXd-BOX c4)) ▸ done


-- auto BOXd(0;1234) | CCZ420: 11 steps
lem-auto-BOXd⟨0·1234⟩-∣-CCZ420 : Complete 4 → ⟪ (Bx⁻0-1234 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Bx⁻0-1234 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CCZ420 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx⁻0-1234 ∷ CCZ024 ∷ []) (CCZ024 ∷ Bx0-2134 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ []) (lem-BOXd-BOX c4) ▸
       at 1 1 (CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 0 1 (Bx0-2143 ∷ []) (lem-sym34-at1221 c4) ▸
       at 0 1 (Bx0-2413 ∷ []) (lem-sym23-at12213443 c4) ▸
       at 0 2 (CCZ024 ∷ Bx0-2413 ∷ []) (sym (lem-Cz-beta-at12243143 c4)) ▸
       at 1 1 (Bx0-2143 ∷ []) (lem-sym23-at12243143 c4) ▸
       at 1 1 (Bx0-2134 ∷ []) (lem-sym34-at12213443 c4) ▸ done

  b1 : Chain (CCZ024 ∷ Bx0-2134 ∷ []) (CCZ024 ∷ Bx⁻0-1234 ∷ [])
  b1 = at 1 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸
       at 0 1 (CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx⁻0-1234 ∷ []) (sym (lem-BOXd-BOX c4)) ▸ done


-- auto BOXd(0;1234) | CSd04: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-CSd04 : Complete 4 → ⟪ (Bx⁻0-1234 ∷ CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS04⁻ ∷ Bx⁻0-1234 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CSd04 c4 = run b0
  where
  b0 : Chain (Bx⁻0-1234 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ Bx⁻0-1234 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ []) (lem-BOXd-BOX c4) ▸
       at 0 1 (Bx0-1243 ∷ []) (lem-sym34 c4) ▸
       at 0 1 (Bx0-1423 ∷ []) (lem-sym23-at3443 c4) ▸
       at 0 2 (CS04⁻ ∷ Bx0-1423 ∷ []) (sym (lem-CS20-beta-ci-at243243 c4)) ▸
       at 1 1 (Bx0-1243 ∷ []) (lem-sym23-at243243 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym34-at3443 c4) ▸
       at 1 1 (Bx⁻0-1234 ∷ []) (sym (lem-BOXd-BOX c4)) ▸ done


-- beta-T @1331: 8 steps
lem-beta-T-at1331 : Complete 4 → ⟪ (Bx0-3214 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) ⟫ʷ
lem-beta-T-at1331 c4 = run b0
  where
  b0 : Chain (Bx0-3214 ∷ []) (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-3124 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·3214⟩ c4) ▸
       at 1 1 (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-beta-T-at132132 c4) ▸
       at 0 2 (Toff023 ∷ Sw12 ∷ []) (lem-nat-1-TOFF013 c4) ▸
       at 1 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 2 2 (Toff023 ∷ Sw12 ∷ []) (lem-nat-1-TOFF013 c4) ▸
       at 3 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 4 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @1331: 5 steps
lem-sym23-at1331 : Complete 4 → ⟪ (Bx0-3214 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ []) ⟫ʷ
lem-sym23-at1331 c4 = run b0
  where
  b0 : Chain (Bx0-3214 ∷ []) (Bx0-3124 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-3124 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·3214⟩ c4) ▸
       at 1 1 (Bx0-3214 ∷ []) (lem-sym23-at132132 c4) ▸
       at 0 2 (Bx0-3124 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·3214⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | CS30 @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS30-at2332 : Complete 4 → ⟪ (Sb⁻0-1-32-4 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS30-at2332 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-32-4 ∷ CS02 ∷ []) (CS02 ∷ Sb⁻0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·32·4⟩ c4) ▸
       at 2 2 (CS03 ∷ Sw23 ∷ []) (lem-nat-2-CS02 c4) ▸
       at 1 2 (CS03 ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS30 c4) ▸
       at 0 2 (CS02 ∷ Sw23 ∷ []) (lem-nat-2-CS03 c4) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | CCZ023: 44 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ023 : Complete 4 → ⟪ (Sb⁻0-1-23-4 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ023 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (run b5)))))
  where
  b0 : Chain (Sb⁻0-1-23-4 ∷ CCZ023 ∷ []) (CS03 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ Toff423 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ [])
  b0 = at 1 1 (CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ []) (lw4 c4 (CCZ023 ∷ []) (CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻0-1-32-4 ∷ []) (lem-SBsymd-at0113203442 c4) ▸
       at 0 2 (CS03 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS20-at2332 c4) ▸
       at 1 1 (Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ Toff423 ∷ Bx⁻0-1324 ∷ []) (refl) ▸
       at 5 1 (Bx0-1324 ∷ []) (lem-BOXd-BOX-at2332 c4) ▸
       at 5 1 (Bx0-3124 ∷ []) (lem-sym12-at2332 c4) ▸
       at 5 1 (Bx0-3214 ∷ []) (lem-sym23-at132132 c4) ▸
       at 5 1 (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) (lem-beta-T-at1331 c4) ▸ done

  b1 : Chain (CS03 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ Toff423 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ []) (CS03 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ Toff423 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CS02 ∷ [])
  b1 = at 8 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 c4) ▸
       at 9 2 (CS03⁻ ∷ CCZ014 ∷ []) (pw2 c4 (CCZ014 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 c4) ▸
       at 7 4 (CX23 ∷ CS03⁻ ∷ CX23 ∷ Toff023 ∷ []) (lw4 c4 (Toff023 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ []) (CX23 ∷ CS03⁻ ∷ CX23 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 c4) ▸
       at 7 2 (CS03⁻ ∷ CCZ014 ∷ []) (pw2 c4 (CCZ014 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 c4) ▸
       at 5 4 (CX23 ∷ CS03⁻ ∷ CX23 ∷ Toff023 ∷ []) (lw4 c4 (Toff023 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ []) (CX23 ∷ CS03⁻ ∷ CX23 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (CS03 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ Toff423 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CS02 ∷ []) (CS03 ∷ Sb0-1-4-2 ∷ Toff423 ∷ CX23 ∷ Sb⁻0-1-4-2 ∷ CS03⁻ ∷ CX23 ∷ Toff423 ∷ Bx⁻0-1324 ∷ CS02 ∷ [])
  b2 = at 8 4 (Bx0-3214 ∷ []) (sym (lem-beta-T-at1331 c4)) ▸
       at 8 1 (Bx0-3124 ∷ []) (lem-sym23-at1331 c4) ▸
       at 8 1 (Bx0-1324 ∷ []) (lem-sym12-at132132 c4) ▸
       at 8 1 (Bx⁻0-1324 ∷ []) (sym (lem-BOXd-BOX-at2332 c4)) ▸
       at 4 4 (CX23 ∷ CS03⁻ ∷ CX23 ∷ Toff423 ∷ []) (pw1 c4 (Toff423 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ []) (CX23 ∷ CS03⁻ ∷ CX23 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CS14⁻ ∷ []) (refl) ▸
       at 3 2 (CX23 ∷ CS14⁻ ∷ []) (lw0 c4 (CS14⁻ ∷ CX23 ∷ []) (CX23 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻0-1-4-2 ∷ []) (refl) ▸ done

  b3 : Chain (CS03 ∷ Sb0-1-4-2 ∷ Toff423 ∷ CX23 ∷ Sb⁻0-1-4-2 ∷ CS03⁻ ∷ CX23 ∷ Toff423 ∷ Bx⁻0-1324 ∷ CS02 ∷ []) (CS03 ∷ CS14 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ Toff423 ∷ Bx⁻0-1324 ∷ CS02 ∷ [])
  b3 = at 4 1 (CS14⁻ ∷ []) (refl) ▸
       at 4 2 (CS03⁻ ∷ CS14⁻ ∷ []) (pw2 c4 (CS14⁻ ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Sb⁻0-1-4-2 ∷ []) (refl) ▸
       at 5 1 (CS14⁻ ∷ []) (refl) ▸
       at 5 2 (CX23 ∷ CS14⁻ ∷ []) (lw0 c4 (CS14⁻ ∷ CX23 ∷ []) (CX23 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sb⁻0-1-4-2 ∷ []) (refl) ▸
       at 2 4 (CX23 ∷ CS03⁻ ∷ CX23 ∷ Toff423 ∷ []) (pw1 c4 (Toff423 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ []) (CX23 ∷ CS03⁻ ∷ CX23 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (CS14 ∷ []) (refl) ▸ done

  b4 : Chain (CS03 ∷ CS14 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ Toff423 ∷ Bx⁻0-1324 ∷ CS02 ∷ []) (CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ Toff423 ∷ Bx⁻0-1324 ∷ CS02 ∷ [])
  b4 = at 1 2 (CX23 ∷ CS14 ∷ []) (lw0 c4 (CS14 ∷ CX23 ∷ []) (CX23 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb0-1-4-2 ∷ []) (refl) ▸
       at 2 1 (CS14 ∷ []) (refl) ▸
       at 2 2 (CS03⁻ ∷ CS14 ∷ []) (pw2 c4 (CS14 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb0-1-4-2 ∷ []) (refl) ▸
       at 3 1 (CS14 ∷ []) (refl) ▸
       at 3 2 (CX23 ∷ CS14 ∷ []) (lw0 c4 (CS14 ∷ CX23 ∷ []) (CX23 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb0-1-4-2 ∷ []) (refl) ▸ done

  b5 : Chain (CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ Toff423 ∷ Bx⁻0-1324 ∷ CS02 ∷ []) (CCZ023 ∷ Sb⁻0-1-23-4 ∷ [])
  b5 = at 4 5 (Sb⁻0-1-32-4 ∷ []) (refl) ▸
       at 4 2 (CS02 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS30-at2332 c4) ▸
       at 5 1 (Sb⁻0-1-23-4 ∷ []) (sym (lem-SBsymd-at0113203442 c4)) ▸
       at 0 5 (CCZ023 ∷ []) (lw4 c4 (CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸ done


-- sym12 @0310243142: 5 steps
lem-sym12-at0310243142 : Complete 4 → ⟪ (Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ []) ⟫ʷ
lem-sym12-at0310243142 c4 = run b0
  where
  b0 : Chain (Bx3-0412 ∷ []) (Bx3-4012 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-0413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0412⟩ c4) ▸
       at 1 1 (Bx2-4013 ∷ []) (lem-sym12-at0210243143 c4) ▸
       at 0 2 (Bx3-4012 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·4013⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | BOX(3;4012): 5 steps
lem-auto-CCZ012-∣-BOX⟨3·4012⟩ : Complete 4 → ⟪ (CCZ012 ∷ Bx3-4012 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·4012⟩ c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Bx3-4012 ∷ []) (Bx3-4012 ∷ CCZ012 ∷ [])
  b0 = at 1 1 (Bx3-0412 ∷ []) (lem-sym12-at0314203142 c4) ▸
       at 1 1 (Bx3-0142 ∷ []) (lem-sym23-at0310243142 c4) ▸
       at 0 2 (Bx3-0142 ∷ CCZ012 ∷ []) (lem-c124-beta-at0310213442 c4) ▸
       at 0 1 (Bx3-0412 ∷ []) (lem-sym23-at0310213442 c4) ▸
       at 0 1 (Bx3-4012 ∷ []) (lem-sym12-at0310243142 c4) ▸ done


-- auto CCZ012 | SBOX(3;4;01;2): 9 steps
lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩ : Complete 4 → ⟪ (CCZ012 ∷ Sb3-4-01-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-01-2 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ012 ∷ Sb3-4-01-2 ∷ []) (Bx3-4012 ∷ Toff201 ∷ Sb3-4-2-1 ∷ Toff201 ∷ Sb⁻3-4-2-1 ∷ CCZ012 ∷ [])
  b0 = at 1 1 (Bx3-4012 ∷ Toff201 ∷ Sb3-4-2-1 ∷ Toff201 ∷ Sb⁻3-4-2-1 ∷ []) (refl) ▸
       at 0 2 (Bx3-4012 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·4012⟩ c4) ▸
       at 3 1 (CS24 ∷ []) (refl) ▸
       at 1 4 (Toff201 ∷ CS24 ∷ Toff201 ∷ CCZ012 ∷ []) (pw3 c4 (CCZ012 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ []) (Toff201 ∷ CS24 ∷ Toff201 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb3-4-2-1 ∷ []) (refl) ▸
       at 5 1 (CS24⁻ ∷ []) (refl) ▸
       at 4 2 (CS24⁻ ∷ CCZ012 ∷ []) (pw3 c4 (CCZ012 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻3-4-2-1 ∷ []) (refl) ▸ done

  b1 : Chain (Bx3-4012 ∷ Toff201 ∷ Sb3-4-2-1 ∷ Toff201 ∷ Sb⁻3-4-2-1 ∷ CCZ012 ∷ []) (Sb3-4-01-2 ∷ CCZ012 ∷ [])
  b1 = at 0 5 (Sb3-4-01-2 ∷ []) (refl) ▸ done


-- auto BOX(0;1234) | CSd34: 9 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd34 : Complete 4 → ⟪ (Bx0-1234 ∷ CS34⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS34⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd34 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-1234 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Bx0-1324 ∷ [])
  b0 = at 0 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 0 1 (Bx0-1342 ∷ []) (lem-sym34-at2332 c4) ▸
       at 0 1 (Bx0-3142 ∷ []) (lem-sym12-at233442 c4) ▸
       at 0 1 (Bx0-3412 ∷ []) (lem-sym23-at13213442 c4) ▸
       at 0 2 (CS34⁻ ∷ Bx0-3412 ∷ []) (sym (lem-CSd12-beta-at13243142 c4)) ▸
       at 1 1 (Bx0-3142 ∷ []) (lem-sym23-at13243142 c4) ▸
       at 1 1 (Bx0-3124 ∷ []) (lem-sym34-at13213442 c4) ▸
       at 1 1 (Bx0-1324 ∷ []) (lem-sym12-at132132 c4) ▸ done

  b1 : Chain (CS34⁻ ∷ Bx0-1324 ∷ []) (CS34⁻ ∷ Bx0-1234 ∷ [])
  b1 = at 1 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸ done


-- auto BOX(0;1234) | CSd34 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd34-at2332 : Complete 4 → ⟪ (Bx0-1324 ∷ CS24⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS24⁻ ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd34-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ c4) ▸
       at 2 2 (CS34⁻ ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS24⁻ ∷ []) (CS34⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS34⁻ ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd34 c4) ▸
       at 0 2 (CS24⁻ ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS34⁻ ∷ []) (CS24⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CCZ432: 26 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ432 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ432 c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Sb0-1-23-4 ∷ CCZ234 ∷ []) (CS24 ∷ Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS34 ∷ [])
  b0 = at 1 1 (CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ []) (lw0 c4 (CCZ234 ∷ []) (CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS24 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS34-at2332 c4) ▸
       at 1 1 (Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ []) (refl) ▸
       at 5 1 (CS14⁻ ∷ []) (refl) ▸
       at 5 4 (CX32 ∷ CS24⁻ ∷ CX32 ∷ CS14⁻ ∷ []) (lw0 c4 (CS14⁻ ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ []) (CX32 ∷ CS24⁻ ∷ CX32 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 8 1 (Sb⁻0-1-4-2 ∷ []) (refl) ▸
       at 4 4 (CX32 ∷ CS24⁻ ∷ CX32 ∷ Toff423 ∷ []) (lw0 c4 (Toff423 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ []) (CX32 ∷ CS24⁻ ∷ CX32 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CS24 ∷ Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS34 ∷ []) (CS24 ∷ CX32 ∷ CCZ134 ∷ CS24⁻ ∷ Bx0-1324 ∷ CX32 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS34 ∷ [])
  b1 = at 3 1 (CS14 ∷ []) (refl) ▸
       at 3 4 (CX32 ∷ CS24⁻ ∷ CX32 ∷ CS14 ∷ []) (lw0 c4 (CS14 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ []) (CX32 ∷ CS24⁻ ∷ CX32 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sb0-1-4-2 ∷ []) (refl) ▸
       at 2 4 (CX32 ∷ CS24⁻ ∷ CX32 ∷ Toff423 ∷ []) (lw0 c4 (Toff423 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ []) (CX32 ∷ CS24⁻ ∷ CX32 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 1 0 (CX32 ∷ CX32 ∷ []) (lw4 c4 [] (CX32 ∷ CX32 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (Bx0-1324 ∷ CCZ134 ∷ []) (lem-CX23-beta-at2332 c4) ▸
       at 2 2 (CCZ134 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at2332 c4) ▸
       at 3 2 (CS24⁻ ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd34-at2332 c4) ▸ done

  b2 : Chain (CS24 ∷ CX32 ∷ CCZ134 ∷ CS24⁻ ∷ Bx0-1324 ∷ CX32 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS34 ∷ []) (CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ Sb0-1-32-4 ∷ [])
  b2 = at 4 0 (CX32 ∷ CX32 ∷ []) (lw4 c4 [] (CX32 ∷ CX32 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (Bx0-1324 ∷ CCZ134 ∷ []) (lem-CX23-beta-at2332 c4) ▸
       at 5 2 (CCZ134 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at2332 c4) ▸
       at 1 2 (CCZ134 ∷ CX32 ∷ []) (lw0 c4 (CX32 ∷ CCZ134 ∷ []) (CCZ134 ∷ CX32 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (CCZ134 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ []) (lw0 c4 (CX32 ∷ CS24⁻ ∷ CX32 ∷ CCZ134 ∷ []) (CCZ134 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ []) tt tt Eq.refl) ▸
       at 1 2 [] (lw0 c4 (CCZ134 ∷ CCZ134 ∷ []) [] tt tt Eq.refl) ▸
       at 4 5 (Sb0-1-32-4 ∷ []) (refl) ▸
       at 4 2 (CS34 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS24-at2332 c4) ▸ done

  b3 : Chain (CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ Sb0-1-32-4 ∷ []) (CCZ234 ∷ Sb0-1-23-4 ∷ [])
  b3 = at 5 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 5 (CCZ234 ∷ []) (lw0 c4 (CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CCZ432 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ432-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ432-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (CCZ234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ234 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ432 c4) ▸
       at 0 2 (CCZ234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | TOFF423: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF423 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF423 c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ Toff423 ∷ []) (Toff423 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 1 1 (K4 ∷ CCZ234 ∷ K4⁻ ∷ []) (lw0 c4 (Toff423 ∷ []) (K4 ∷ CCZ234 ∷ K4⁻ ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (K4 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at2332 c4) ▸
       at 1 2 (CCZ234 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ432-at2332 c4) ▸
       at 2 2 (K4⁻ ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd4-at2332 c4) ▸
       at 3 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 3 (Toff423 ∷ []) (lw0 c4 (K4 ∷ CCZ234 ∷ K4⁻ ∷ []) (Toff423 ∷ []) tt tt Eq.refl) ▸ done


-- auto CSd01 | BOX(2;0134): 1 steps
lem-auto-CSd01-∣-BOX⟨2·0134⟩ : Complete 4 → ⟪ (CS01⁻ ∷ Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ CS01⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨2·0134⟩ c4 = run b0
  where
  b0 : Chain (CS01⁻ ∷ Bx2-0134 ∷ []) (Bx2-0134 ∷ CS01⁻ ∷ [])
  b0 = at 0 2 (Bx2-0134 ∷ CS01⁻ ∷ []) (lem-CSd12-beta-at021021 c4) ▸ done


-- auto S0 | BOX(1;0234): 6 steps
lem-auto-S0-∣-BOX⟨1·0234⟩ : Complete 4 → ⟪ (S0 ∷ Bx1-0234 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0234 ∷ S0 ∷ []) ⟫ʷ
lem-auto-S0-∣-BOX⟨1·0234⟩ c4 = run b0
  where
  b0 : Chain (S0 ∷ Bx1-0234 ∷ []) (Bx1-0234 ∷ S0 ∷ [])
  b0 = at 1 1 (Toff102 ∷ CCZ134 ∷ Toff102 ∷ CCZ134 ∷ []) (lem-beta-T-at0110 c4) ▸
       at 0 2 (Toff102 ∷ S0 ∷ []) (lw4 c4 (S0 ∷ Toff102 ∷ []) (Toff102 ∷ S0 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ134 ∷ S0 ∷ []) (c₁ (S) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑)) ▸
       at 2 2 (Toff102 ∷ S0 ∷ []) (lw4 c4 (S0 ∷ Toff102 ∷ []) (Toff102 ∷ S0 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ134 ∷ S0 ∷ []) (c₁ (S) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑)) ▸
       at 0 4 (Bx1-0234 ∷ []) (sym (lem-beta-T-at0110 c4)) ▸ done


-- auto SBOX(0;1;23;4) | CS20 CS20: 6 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS20-CS20 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CS02 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CS02 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS20-CS20 c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ CS02 ∷ CS02 ∷ []) (CS02 ∷ CS02 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS02 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS30-at2332 c4) ▸
       at 1 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 1 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 1 2 (CS02 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS30-at2332 c4) ▸
       at 2 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸ done


-- auto SBOX(0;1;23;4) | CS20 CS20 @2332: 9 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS20-CS20-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ CS03 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ CS03 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS20-CS20-at2332 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-32-4 ∷ CS03 ∷ CS03 ∷ []) (CS03 ∷ CS03 ∷ Sb0-1-32-4 ∷ Sw23 ∷ Sw23 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (CS02 ∷ Sw23 ∷ []) (lem-nat-2-CS03 c4) ▸
       at 3 2 (CS02 ∷ Sw23 ∷ []) (lem-nat-2-CS03 c4) ▸
       at 1 3 (CS02 ∷ CS02 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS20-CS20 c4) ▸
       at 0 2 (CS03 ∷ Sw23 ∷ []) (lem-nat-2-CS02 c4) ▸
       at 1 2 (CS03 ∷ Sw23 ∷ []) (lem-nat-2-CS02 c4) ▸
       at 2 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸ done

  b1 : Chain (CS03 ∷ CS03 ∷ Sb0-1-32-4 ∷ Sw23 ∷ Sw23 ∷ []) (CS03 ∷ CS03 ∷ Sb0-1-32-4 ∷ [])
  b1 = at 3 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CZ30: 5 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CZ30 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CZ03 ∷ []) ⟫ʷ ≈ ⟪ (CZ03 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CZ30 c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ CZ03 ∷ []) (CZ03 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 1 1 (CS03 ∷ CS03 ∷ []) (lw4 c4 (CZ03 ∷ []) (CS03 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 3 (CS03 ∷ CS03 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS20-CS20-at2332 c4) ▸
       at 2 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 2 (CZ03 ∷ []) (lw4 c4 (CS03 ∷ CS03 ∷ []) (CZ03 ∷ []) tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CZ30 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CZ30-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ CZ02 ∷ []) ⟫ʷ ≈ ⟪ (CZ02 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CZ30-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CZ02 ∷ []) (CZ02 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (CZ03 ∷ Sw23 ∷ []) (lem-nat-2-CZ02 c4) ▸
       at 1 2 (CZ03 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CZ30 c4) ▸
       at 0 2 (CZ02 ∷ Sw23 ∷ []) (lem-nat-2-CZ03 c4) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CX20: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CX20 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CX20 ∷ []) ⟫ʷ ≈ ⟪ (CX20 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CX20 c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ CX20 ∷ []) (CX20 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 1 1 (K0 ∷ CZ02 ∷ K0⁻ ∷ []) (lw4 c4 (CX20 ∷ []) (K0 ∷ CZ02 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (K0 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at2332 c4) ▸
       at 1 2 (CZ02 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CZ30-at2332 c4) ▸
       at 2 2 (K0⁻ ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd0-at2332 c4) ▸
       at 3 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 3 (CX20 ∷ []) (lw4 c4 (K0 ∷ CZ02 ∷ K0⁻ ∷ []) (CX20 ∷ []) tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CSd20: 11 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd20 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd20 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-23-4 ∷ CS02⁻ ∷ []) (Bx0-1234 ∷ Toff423 ∷ CS02⁻ ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 1 (CS14⁻ ∷ []) (refl) ▸
       at 4 2 (CS02⁻ ∷ CS14⁻ ∷ []) (pw3 c4 (CS14⁻ ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 3 2 (CS02⁻ ∷ Toff423 ∷ []) (pw1 c4 (Toff423 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CS14 ∷ []) (refl) ▸
       at 2 2 (CS02⁻ ∷ CS14 ∷ []) (pw3 c4 (CS14 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb0-1-4-3 ∷ []) (refl) ▸ done

  b1 : Chain (Bx0-1234 ∷ Toff423 ∷ CS02⁻ ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (CS02⁻ ∷ Sb0-1-23-4 ∷ [])
  b1 = at 1 2 (CS02⁻ ∷ Toff423 ∷ []) (pw1 c4 (Toff423 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (CS02⁻ ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd20 c4) ▸
       at 1 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- auto SBOX(0;1;23;4) | CS30 CS30: 6 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS30-CS30 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CS03 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ CS03 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS30-CS30 c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ CS03 ∷ CS03 ∷ []) (CS03 ∷ CS03 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS03 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS20-at2332 c4) ▸
       at 1 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 1 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 1 2 (CS03 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS20-at2332 c4) ▸
       at 2 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸ done


-- auto SBOX(0;1;23;4) | CS30 CS30 @2332: 9 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS30-CS30-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ CS02 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CS02 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS30-CS30-at2332 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-32-4 ∷ CS02 ∷ CS02 ∷ []) (CS02 ∷ CS02 ∷ Sb0-1-32-4 ∷ Sw23 ∷ Sw23 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (CS03 ∷ Sw23 ∷ []) (lem-nat-2-CS02 c4) ▸
       at 3 2 (CS03 ∷ Sw23 ∷ []) (lem-nat-2-CS02 c4) ▸
       at 1 3 (CS03 ∷ CS03 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS30-CS30 c4) ▸
       at 0 2 (CS02 ∷ Sw23 ∷ []) (lem-nat-2-CS03 c4) ▸
       at 1 2 (CS02 ∷ Sw23 ∷ []) (lem-nat-2-CS03 c4) ▸
       at 2 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸ done

  b1 : Chain (CS02 ∷ CS02 ∷ Sb0-1-32-4 ∷ Sw23 ∷ Sw23 ∷ []) (CS02 ∷ CS02 ∷ Sb0-1-32-4 ∷ [])
  b1 = at 3 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CZ20: 5 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CZ20 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CZ02 ∷ []) ⟫ʷ ≈ ⟪ (CZ02 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CZ20 c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ CZ02 ∷ []) (CZ02 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 1 1 (CS02 ∷ CS02 ∷ []) (lw4 c4 (CZ02 ∷ []) (CS02 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 3 (CS02 ∷ CS02 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS30-CS30-at2332 c4) ▸
       at 2 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 2 (CZ02 ∷ []) (lw4 c4 (CS02 ∷ CS02 ∷ []) (CZ02 ∷ []) tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CZ20 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CZ20-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ CZ03 ∷ []) ⟫ʷ ≈ ⟪ (CZ03 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CZ20-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CZ03 ∷ []) (CZ03 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (CZ02 ∷ Sw23 ∷ []) (lem-nat-2-CZ03 c4) ▸
       at 1 2 (CZ02 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CZ20 c4) ▸
       at 0 2 (CZ03 ∷ Sw23 ∷ []) (lem-nat-2-CZ02 c4) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CX30: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CX30 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CX30 ∷ []) ⟫ʷ ≈ ⟪ (CX30 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CX30 c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ CX30 ∷ []) (CX30 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 1 1 (K0 ∷ CZ03 ∷ K0⁻ ∷ []) (lw4 c4 (CX30 ∷ []) (K0 ∷ CZ03 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (K0 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at2332 c4) ▸
       at 1 2 (CZ03 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CZ20-at2332 c4) ▸
       at 2 2 (K0⁻ ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd0-at2332 c4) ▸
       at 3 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 3 (CX30 ∷ []) (lw4 c4 (K0 ∷ CZ03 ∷ K0⁻ ∷ []) (CX30 ∷ []) tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CSd30: 11 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd30 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd30 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-23-4 ∷ CS03⁻ ∷ []) (Bx0-1234 ∷ Toff423 ∷ CS03⁻ ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 1 (CS14⁻ ∷ []) (refl) ▸
       at 4 2 (CS03⁻ ∷ CS14⁻ ∷ []) (pw2 c4 (CS14⁻ ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 3 2 (CS03⁻ ∷ Toff423 ∷ []) (pw1 c4 (Toff423 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CS14 ∷ []) (refl) ▸
       at 2 2 (CS03⁻ ∷ CS14 ∷ []) (pw2 c4 (CS14 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb0-1-4-3 ∷ []) (refl) ▸ done

  b1 : Chain (Bx0-1234 ∷ Toff423 ∷ CS03⁻ ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (CS03⁻ ∷ Sb0-1-23-4 ∷ [])
  b1 = at 1 2 (CS03⁻ ∷ Toff423 ∷ []) (pw1 c4 (Toff423 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (CS03⁻ ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd30 c4) ▸
       at 1 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- auto CCZ012 | BOX(0;3412): 9 steps
lem-auto-CCZ012-∣-BOX⟨0·3412⟩ : Complete 4 → ⟪ (CCZ012 ∷ Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨0·3412⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ012 ∷ Bx0-3412 ∷ []) (Bx0-3142 ∷ CCZ012 ∷ [])
  b0 = at 1 1 (Bx0-3142 ∷ []) (lem-sym23-at13243142 c4) ▸
       at 1 1 (Bx0-3124 ∷ []) (lem-sym34-at13213442 c4) ▸
       at 1 1 (Bx0-1324 ∷ []) (lem-sym12-at132132 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸
       at 0 2 (Bx0-1234 ∷ CCZ012 ∷ []) (lem-Cz-beta c4) ▸
       at 0 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 0 1 (Bx0-1342 ∷ []) (lem-sym34-at2332 c4) ▸
       at 0 1 (Bx0-3142 ∷ []) (lem-sym12-at233442 c4) ▸ done

  b1 : Chain (Bx0-3142 ∷ CCZ012 ∷ []) (Bx0-3412 ∷ CCZ012 ∷ [])
  b1 = at 0 1 (Bx0-3412 ∷ []) (lem-sym23-at13213442 c4) ▸ done


-- sym23 @0113243042: 5 steps
lem-sym23-at0113243042 : Complete 4 → ⟪ (Bx1-3402 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3042 ∷ []) ⟫ʷ
lem-sym23-at0113243042 c4 = run b0
  where
  b0 : Chain (Bx1-3402 ∷ []) (Bx1-3042 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-3412 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·3402⟩ c4) ▸
       at 1 1 (Bx0-3142 ∷ []) (lem-sym23-at13243142 c4) ▸
       at 0 2 (Bx1-3042 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·3142⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @0213243041: 5 steps
lem-sym23-at0213243041 : Complete 4 → ⟪ (Bx2-3401 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3041 ∷ []) ⟫ʷ
lem-sym23-at0213243041 c4 = run b0
  where
  b0 : Chain (Bx2-3401 ∷ []) (Bx2-3041 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-3402 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·3401⟩ c4) ▸
       at 1 1 (Bx1-3042 ∷ []) (lem-sym23-at0113243042 c4) ▸
       at 0 2 (Bx2-3041 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·3042⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @0213243140: 5 steps
lem-sym23-at0213243140 : Complete 4 → ⟪ (Bx2-3410 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3140 ∷ []) ⟫ʷ
lem-sym23-at0213243140 c4 = run b0
  where
  b0 : Chain (Bx2-3410 ∷ []) (Bx2-3140 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-3401 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·3410⟩ c4) ▸
       at 1 1 (Bx2-3041 ∷ []) (lem-sym23-at0213243041 c4) ▸
       at 0 2 (Bx2-3140 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·3041⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym34 @0113203442: 5 steps
lem-sym34-at0113203442 : Complete 4 → ⟪ (Bx1-3042 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3024 ∷ []) ⟫ʷ
lem-sym34-at0113203442 c4 = run b0
  where
  b0 : Chain (Bx1-3042 ∷ []) (Bx1-3024 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-3142 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·3042⟩ c4) ▸
       at 1 1 (Bx0-3124 ∷ []) (lem-sym34-at13213442 c4) ▸
       at 0 2 (Bx1-3024 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·3124⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym34 @0213203441: 5 steps
lem-sym34-at0213203441 : Complete 4 → ⟪ (Bx2-3041 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3014 ∷ []) ⟫ʷ
lem-sym34-at0213203441 c4 = run b0
  where
  b0 : Chain (Bx2-3041 ∷ []) (Bx2-3014 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-3042 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·3041⟩ c4) ▸
       at 1 1 (Bx1-3024 ∷ []) (lem-sym34-at0113203442 c4) ▸
       at 0 2 (Bx2-3014 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·3024⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym34 @0213213440: 5 steps
lem-sym34-at0213213440 : Complete 4 → ⟪ (Bx2-3140 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3104 ∷ []) ⟫ʷ
lem-sym34-at0213213440 c4 = run b0
  where
  b0 : Chain (Bx2-3140 ∷ []) (Bx2-3104 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-3041 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·3140⟩ c4) ▸
       at 1 1 (Bx2-3014 ∷ []) (lem-sym34-at0213203441 c4) ▸
       at 0 2 (Bx2-3104 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·3014⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- Cz-beta @0110: 7 steps
lem-Cz-beta-at0110 : Complete 4 → ⟪ (CCZ012 ∷ Bx1-0234 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0234 ∷ CCZ012 ∷ []) ⟫ʷ
lem-Cz-beta-at0110 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Bx1-0234 ∷ []) (Bx1-0234 ∷ CCZ012 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-1234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0234⟩ c4) ▸
       at 1 2 (Bx0-1234 ∷ CCZ012 ∷ []) (lem-Cz-beta c4) ▸
       at 0 2 (Bx1-0234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1234⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- Cz-beta @021021: 7 steps
lem-Cz-beta-at021021 : Complete 4 → ⟪ (CCZ012 ∷ Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ CCZ012 ∷ []) ⟫ʷ
lem-Cz-beta-at021021 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Bx2-0134 ∷ []) (Bx2-0134 ∷ CCZ012 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0134⟩ c4) ▸
       at 1 2 (Bx1-0234 ∷ CCZ012 ∷ []) (lem-Cz-beta-at0110 c4) ▸
       at 0 2 (Bx2-0134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0234⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- Cz-beta @0220: 7 steps
lem-Cz-beta-at0220 : Complete 4 → ⟪ (CCZ012 ∷ Bx2-1034 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1034 ∷ CCZ012 ∷ []) ⟫ʷ
lem-Cz-beta-at0220 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Bx2-1034 ∷ []) (Bx2-1034 ∷ CCZ012 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx2-0134 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1034⟩ c4) ▸
       at 1 2 (Bx2-0134 ∷ CCZ012 ∷ []) (lem-Cz-beta-at021021 c4) ▸
       at 0 2 (Bx2-1034 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·0134⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym34 @022330: 5 steps
lem-sym34-at022330 : Complete 4 → ⟪ (Bx2-1304 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1340 ∷ []) ⟫ʷ
lem-sym34-at022330 c4 = run b0
  where
  b0 : Chain (Bx2-1304 ∷ []) (Bx2-1340 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-0314 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1304⟩ c4) ▸
       at 1 1 (Bx2-0341 ∷ []) (lem-sym34-at02102331 c4) ▸
       at 0 2 (Bx2-1340 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·0341⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym12 @02233440: 5 steps
lem-sym12-at02233440 : Complete 4 → ⟪ (Bx2-1340 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3140 ∷ []) ⟫ʷ
lem-sym12-at02233440 c4 = run b0
  where
  b0 : Chain (Bx2-1340 ∷ []) (Bx2-3140 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-0341 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1340⟩ c4) ▸
       at 1 1 (Bx2-3041 ∷ []) (lem-sym12-at0210233441 c4) ▸
       at 0 2 (Bx2-3140 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·3041⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @0113203442: 5 steps
lem-sym23-at0113203442 : Complete 4 → ⟪ (Bx1-3042 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3402 ∷ []) ⟫ʷ
lem-sym23-at0113203442 c4 = run b0
  where
  b0 : Chain (Bx1-3042 ∷ []) (Bx1-3402 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-3142 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·3042⟩ c4) ▸
       at 1 1 (Bx0-3412 ∷ []) (lem-sym23-at13213442 c4) ▸
       at 0 2 (Bx1-3402 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·3412⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @0213203441: 5 steps
lem-sym23-at0213203441 : Complete 4 → ⟪ (Bx2-3041 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3401 ∷ []) ⟫ʷ
lem-sym23-at0213203441 c4 = run b0
  where
  b0 : Chain (Bx2-3041 ∷ []) (Bx2-3401 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-3042 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·3041⟩ c4) ▸
       at 1 1 (Bx1-3402 ∷ []) (lem-sym23-at0113203442 c4) ▸
       at 0 2 (Bx2-3401 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·3402⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @0213213440: 5 steps
lem-sym23-at0213213440 : Complete 4 → ⟪ (Bx2-3140 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3410 ∷ []) ⟫ʷ
lem-sym23-at0213213440 c4 = run b0
  where
  b0 : Chain (Bx2-3140 ∷ []) (Bx2-3410 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-3041 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·3140⟩ c4) ▸
       at 1 1 (Bx2-3401 ∷ []) (lem-sym23-at0213203441 c4) ▸
       at 0 2 (Bx2-3410 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·3401⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | BOX(2;3410): 11 steps
lem-auto-CCZ012-∣-BOX⟨2·3410⟩ : Complete 4 → ⟪ (CCZ012 ∷ Bx2-3410 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3410 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨2·3410⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ012 ∷ Bx2-3410 ∷ []) (Bx2-1340 ∷ CCZ012 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx2-3140 ∷ []) (lem-sym23-at0213243140 c4) ▸
       at 1 1 (Bx2-3104 ∷ []) (lem-sym34-at0213213440 c4) ▸
       at 1 1 (Bx2-1304 ∷ []) (lem-sym12-at02132130 c4) ▸
       at 1 1 (Bx2-1034 ∷ []) (lem-sym23-at022330 c4) ▸
       at 0 2 (Bx2-1034 ∷ CCZ012 ∷ []) (lem-Cz-beta-at0220 c4) ▸
       at 0 1 (Bx2-1304 ∷ []) (lem-sym23-at0220 c4) ▸
       at 0 1 (Bx2-1340 ∷ []) (lem-sym34-at022330 c4) ▸ done

  b1 : Chain (Bx2-1340 ∷ CCZ012 ∷ []) (Bx2-3410 ∷ CCZ012 ∷ [])
  b1 = at 0 1 (Bx2-3140 ∷ []) (lem-sym12-at02233440 c4) ▸
       at 0 1 (Bx2-3410 ∷ []) (lem-sym23-at0213213440 c4) ▸
       at 1 1 (CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸ done


-- auto CS01 | BOX(1;0234): 5 steps
lem-auto-CS01-∣-BOX⟨1·0234⟩ : Complete 4 → ⟪ (CS01 ∷ Bx1-0234 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0234 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨1·0234⟩ c4 = run b0
  where
  b0 : Chain (CS01 ∷ Bx1-0234 ∷ []) (Bx1-0234 ∷ CS01 ∷ [])
  b0 = at 0 1 (CS01 ∷ []) (lw4 c4 (CS01 ∷ []) (CS01 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx1-2034 ∷ []) (lem-sym12-at0110 c4) ▸
       at 0 2 (Bx1-2034 ∷ CS01 ∷ []) (lem-CS20-beta-c-at011220 c4) ▸
       at 0 1 (Bx1-0234 ∷ []) (lem-sym12-at011220 c4) ▸
       at 1 1 (CS01 ∷ []) (lw4 c4 (CS01 ∷ []) (CS01 ∷ []) tt tt Eq.refl) ▸ done


-- auto CS01 | TOFF234: 1 steps
lem-auto-CS01-∣-TOFF234 : Complete 4 → ⟪ (CS01 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-TOFF234 c4 = run b0
  where
  b0 : Chain (CS01 ∷ Toff234 ∷ []) (Toff234 ∷ CS01 ∷ [])
  b0 = at 0 2 (Toff234 ∷ CS01 ∷ []) (c₂ (CS) (Toff)) ▸ done


-- auto CS01 | TOFF234 @2332: 7 steps
lem-auto-CS01-∣-TOFF234-at2332 : Complete 4 → ⟪ (CS01 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-TOFF234-at2332 c4 = run b0
  where
  b0 : Chain (CS01 ∷ Toff324 ∷ []) (Toff324 ∷ CS01 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS01 ∷ Sw23 ∷ []) (sym (c₂ (CS) (Swap))) ▸
       at 2 2 (Toff234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ Toff324 ∷ []) (Toff234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff234 ∷ CS01 ∷ []) (lem-auto-CS01-∣-TOFF234 c4) ▸
       at 0 2 (Toff324 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ Toff234 ∷ []) (Toff324 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS01 ∷ Sw23 ∷ []) (sym (c₂ (CS) (Swap))) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CS01 | TOFF234 @243243: 7 steps
lem-auto-CS01-∣-TOFF234-at243243 : Complete 4 → ⟪ (CS01 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-TOFF234-at243243 c4 = run b0
  where
  b0 : Chain (CS01 ∷ Toff423 ∷ []) (Toff423 ∷ CS01 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 2 2 (Toff324 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff423 ∷ []) (Toff324 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff324 ∷ CS01 ∷ []) (lem-auto-CS01-∣-TOFF234-at2332 c4) ▸
       at 0 2 (Toff423 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff324 ∷ []) (Toff423 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CS01 | SBOX(1;0;23;4): 11 steps
lem-auto-CS01-∣-SBOX⟨1·0·23·4⟩ : Complete 4 → ⟪ (CS01 ∷ Sb1-0-23-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-23-4 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨1·0·23·4⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS01 ∷ Sb1-0-23-4 ∷ []) (Bx1-0234 ∷ Toff423 ∷ Sb1-0-4-3 ∷ Toff423 ∷ CS01 ∷ CS04⁻ ∷ [])
  b0 = at 1 1 (Bx1-0234 ∷ Toff423 ∷ Sb1-0-4-3 ∷ Toff423 ∷ Sb⁻1-0-4-3 ∷ []) (refl) ▸
       at 0 2 (Bx1-0234 ∷ CS01 ∷ []) (lem-auto-CS01-∣-BOX⟨1·0234⟩ c4) ▸
       at 1 2 (Toff423 ∷ CS01 ∷ []) (lem-auto-CS01-∣-TOFF234-at243243 c4) ▸
       at 3 1 (CS04 ∷ []) (refl) ▸
       at 2 2 (CS04 ∷ CS01 ∷ []) (pw2 c4 (CS01 ∷ CS04 ∷ []) (CS04 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb1-0-4-3 ∷ []) (refl) ▸
       at 3 2 (Toff423 ∷ CS01 ∷ []) (lem-auto-CS01-∣-TOFF234-at243243 c4) ▸
       at 5 1 (CS04⁻ ∷ []) (refl) ▸ done

  b1 : Chain (Bx1-0234 ∷ Toff423 ∷ Sb1-0-4-3 ∷ Toff423 ∷ CS01 ∷ CS04⁻ ∷ []) (Sb1-0-23-4 ∷ CS01 ∷ [])
  b1 = at 4 2 (CS04⁻ ∷ CS01 ∷ []) (pw2 c4 (CS01 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻1-0-4-3 ∷ []) (refl) ▸
       at 0 5 (Sb1-0-23-4 ∷ []) (refl) ▸ done


-- auto CX01 | BOX(1;0234): 1 steps
lem-auto-CX01-∣-BOX⟨1·0234⟩ : Complete 4 → ⟪ (CX01 ∷ Bx1-0234 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0234 ∷ CX01 ∷ []) ⟫ʷ
lem-auto-CX01-∣-BOX⟨1·0234⟩ c4 = run b0
  where
  b0 : Chain (CX01 ∷ Bx1-0234 ∷ []) (Bx1-0234 ∷ CX01 ∷ [])
  b0 = at 0 2 (Bx1-0234 ∷ CX01 ∷ []) (lem-CX10-beta-c-at0110 c4) ▸ done


-- auto CX01 | TOFF234: 1 steps
lem-auto-CX01-∣-TOFF234 : Complete 4 → ⟪ (CX01 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ CX01 ∷ []) ⟫ʷ
lem-auto-CX01-∣-TOFF234 c4 = run b0
  where
  b0 : Chain (CX01 ∷ Toff234 ∷ []) (Toff234 ∷ CX01 ∷ [])
  b0 = at 0 2 (Toff234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Toff)) ▸ done


-- F0 @143143: 5 steps
lem-F0-at143143 : Complete 4 → ⟪ (Sb2-0-34-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-34-2 ∷ []) ⟫ʷ
lem-F0-at143143 c4 = run b0
  where
  b0 : Chain (Sb2-0-34-1 ∷ []) (Sb1-0-34-2 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb1-0-34-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·34·1⟩ c4) ▸
       at 1 1 (Sb2-0-34-1 ∷ []) (lem-F0-at14213243 c4) ▸
       at 0 2 (Sb1-0-34-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·34·1⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CX01 | BOX(1;0234) @3443: 7 steps
lem-auto-CX01-∣-BOX⟨1·0234⟩-at3443 : Complete 4 → ⟪ (CX01 ∷ Bx1-0243 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0243 ∷ CX01 ∷ []) ⟫ʷ
lem-auto-CX01-∣-BOX⟨1·0234⟩-at3443 c4 = run b0
  where
  b0 : Chain (CX01 ∷ Bx1-0243 ∷ []) (Bx1-0243 ∷ CX01 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 2 2 (Bx1-0234 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·0243⟩ c4) ▸
       at 1 2 (Bx1-0234 ∷ CX01 ∷ []) (lem-auto-CX01-∣-BOX⟨1·0234⟩ c4) ▸
       at 0 2 (Bx1-0243 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·0234⟩ c4) ▸
       at 1 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CX01 | BOX(1;0234) @233442: 7 steps
lem-auto-CX01-∣-BOX⟨1·0234⟩-at233442 : Complete 4 → ⟪ (CX01 ∷ Bx1-0342 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0342 ∷ CX01 ∷ []) ⟫ʷ
lem-auto-CX01-∣-BOX⟨1·0234⟩-at233442 c4 = run b0
  where
  b0 : Chain (CX01 ∷ Bx1-0342 ∷ []) (Bx1-0342 ∷ CX01 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 2 2 (Bx1-0243 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0342⟩ c4) ▸
       at 1 2 (Bx1-0243 ∷ CX01 ∷ []) (lem-auto-CX01-∣-BOX⟨1·0234⟩-at3443 c4) ▸
       at 0 2 (Bx1-0342 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0243⟩ c4) ▸
       at 1 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CX01 | SBOX(2;0;34;1): 13 steps
lem-auto-CX01-∣-SBOX⟨2·0·34·1⟩ : Complete 4 → ⟪ (CX01 ∷ Sb2-0-34-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-34-1 ∷ CX01 ∷ []) ⟫ʷ
lem-auto-CX01-∣-SBOX⟨2·0·34·1⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX01 ∷ Sb2-0-34-1 ∷ []) (Bx1-0342 ∷ Toff234 ∷ Sb1-0-2-4 ∷ Toff234 ∷ CX01 ∷ Sb⁻1-0-2-4 ∷ [])
  b0 = at 1 1 (Sb1-0-34-2 ∷ []) (lem-F0-at143143 c4) ▸
       at 1 1 (Bx1-0342 ∷ Toff234 ∷ Sb1-0-2-4 ∷ Toff234 ∷ Sb⁻1-0-2-4 ∷ []) (refl) ▸
       at 0 2 (Bx1-0342 ∷ CX01 ∷ []) (lem-auto-CX01-∣-BOX⟨1·0234⟩-at233442 c4) ▸
       at 1 2 (Toff234 ∷ CX01 ∷ []) (lem-auto-CX01-∣-TOFF234 c4) ▸
       at 3 1 (CS02 ∷ []) (refl) ▸
       at 2 2 (CS02 ∷ CX01 ∷ []) (lw4 c4 (CX01 ∷ CS02 ∷ []) (CS02 ∷ CX01 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb1-0-2-4 ∷ []) (refl) ▸
       at 3 2 (Toff234 ∷ CX01 ∷ []) (lem-auto-CX01-∣-TOFF234 c4) ▸ done

  b1 : Chain (Bx1-0342 ∷ Toff234 ∷ Sb1-0-2-4 ∷ Toff234 ∷ CX01 ∷ Sb⁻1-0-2-4 ∷ []) (Sb2-0-34-1 ∷ CX01 ∷ [])
  b1 = at 5 1 (CS02⁻ ∷ []) (refl) ▸
       at 4 2 (CS02⁻ ∷ CX01 ∷ []) (lw4 c4 (CX01 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CX01 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻1-0-2-4 ∷ []) (refl) ▸
       at 0 5 (Sb1-0-34-2 ∷ []) (refl) ▸
       at 0 1 (Sb2-0-34-1 ∷ []) (sym (lem-F0-at143143 c4)) ▸ done


-- auto CS01 | BOX(0;1234): 3 steps
lem-auto-CS01-∣-BOX⟨0·1234⟩ : Complete 4 → ⟪ (CS01 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨0·1234⟩ c4 = run b0
  where
  b0 : Chain (CS01 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CS01 ∷ [])
  b0 = at 1 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 0 2 (Bx0-2134 ∷ CS01 ∷ []) (lem-CS20-beta-c-at1221 c4) ▸
       at 0 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸ done


-- auto CS01 | SBOX(0;1;23;4): 11 steps
lem-auto-CS01-∣-SBOX⟨0·1·23·4⟩ : Complete 4 → ⟪ (CS01 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-23-4 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨0·1·23·4⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS01 ∷ Sb0-1-23-4 ∷ []) (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ CS01 ∷ CS14⁻ ∷ [])
  b0 = at 1 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 0 2 (Bx0-1234 ∷ CS01 ∷ []) (lem-auto-CS01-∣-BOX⟨0·1234⟩ c4) ▸
       at 1 2 (Toff423 ∷ CS01 ∷ []) (lem-auto-CS01-∣-TOFF234-at243243 c4) ▸
       at 3 1 (CS14 ∷ []) (refl) ▸
       at 2 2 (CS14 ∷ CS01 ∷ []) (pw2 c4 (CS01 ∷ CS14 ∷ []) (CS14 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb0-1-4-3 ∷ []) (refl) ▸
       at 3 2 (Toff423 ∷ CS01 ∷ []) (lem-auto-CS01-∣-TOFF234-at243243 c4) ▸
       at 5 1 (CS14⁻ ∷ []) (refl) ▸ done

  b1 : Chain (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ CS01 ∷ CS14⁻ ∷ []) (Sb0-1-23-4 ∷ CS01 ∷ [])
  b1 = at 4 2 (CS14⁻ ∷ CS01 ∷ []) (pw2 c4 (CS01 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- sym34 @02233440: 5 steps
lem-sym34-at02233440 : Complete 4 → ⟪ (Bx2-1340 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1304 ∷ []) ⟫ʷ
lem-sym34-at02233440 c4 = run b0
  where
  b0 : Chain (Bx2-1340 ∷ []) (Bx2-1304 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-0341 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1340⟩ c4) ▸
       at 1 1 (Bx2-0314 ∷ []) (lem-sym34-at0210233441 c4) ▸
       at 0 2 (Bx2-1304 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·0314⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- CS12-beta @0220: 7 steps
lem-CS12-beta-at0220 : Complete 4 → ⟪ (CS01 ∷ Bx2-1034 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1034 ∷ CS01 ∷ []) ⟫ʷ
lem-CS12-beta-at0220 c4 = run b0
  where
  b0 : Chain (CS01 ∷ Bx2-1034 ∷ []) (Bx2-1034 ∷ CS01 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS01 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS01 ∷ []) (CS01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx2-0134 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1034⟩ c4) ▸
       at 1 2 (Bx2-0134 ∷ CS01 ∷ []) (lem-CS12-beta-at021021 c4) ▸
       at 0 2 (Bx2-1034 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·0134⟩ c4) ▸
       at 1 2 (CS01 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS01 ∷ []) (CS01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CS01 | BOX(2;1340): 7 steps
lem-auto-CS01-∣-BOX⟨2·1340⟩ : Complete 4 → ⟪ (CS01 ∷ Bx2-1340 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1340 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·1340⟩ c4 = run b0
  where
  b0 : Chain (CS01 ∷ Bx2-1340 ∷ []) (Bx2-1340 ∷ CS01 ∷ [])
  b0 = at 0 1 (CS01 ∷ []) (lw4 c4 (CS01 ∷ []) (CS01 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx2-1304 ∷ []) (lem-sym34-at02233440 c4) ▸
       at 1 1 (Bx2-1034 ∷ []) (lem-sym23-at022330 c4) ▸
       at 0 2 (Bx2-1034 ∷ CS01 ∷ []) (lem-CS12-beta-at0220 c4) ▸
       at 0 1 (Bx2-1304 ∷ []) (lem-sym23-at0220 c4) ▸
       at 0 1 (Bx2-1340 ∷ []) (lem-sym34-at022330 c4) ▸
       at 1 1 (CS01 ∷ []) (lw4 c4 (CS01 ∷ []) (CS01 ∷ []) tt tt Eq.refl) ▸ done


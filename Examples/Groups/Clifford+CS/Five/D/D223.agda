{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D223 where

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
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-BOXd-BOX ; lem-Cz-beta ; lem-beta-T-at2332 ; lem-c124-beta ; lem-sym12 ; lem-sym23 ; lem-sym34)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-c124-beta-at3443 ; lem-sym12-at1221 ; lem-sym23-at1221)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-CX10-beta-c-at0110 ; lem-Cz-beta-at2332 ; lem-F0d ; lem-T312-beta-at01122330 ; lem-beta-T-at122331 ; lem-c124-beta-at2332 ; lem-sym12-at0110 ; lem-sym12-at011220 ; lem-sym12-at0112203443 ; lem-sym23-at011220 ; lem-sym23-at01122330 ; lem-sym23-at122331 ; lem-sym23-at2332 ; lem-sym34-at011220 ; lem-sym34-at12213443 ; lem-sym34-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-BOXd-BOX-at132132 ; lem-BOXd-BOX-at2332 ; lem-sym23-at0110 ; lem-sym23-at021021)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-sym23-at01102332 ; lem-sym34-at0110233442 ; lem-sym34-at0210233441)
open import Examples.Groups.Clifford+CS.Five.D.D007 using (lem-CS12-beta-at021021 ; lem-sym23-at02102331 ; lem-sym34-at01102332 ; lem-sym34-at02102331)
open import Examples.Groups.Clifford+CS.Five.D.D008 using (lem-SBsymd-at0113203442)
open import Examples.Groups.Clifford+CS.Five.D.D010 using (lem-sym12-at02102331 ; lem-sym12-at02132031)
open import Examples.Groups.Clifford+CS.Five.D.D011 using (lem-CS20-beta-c-at011220)
open import Examples.Groups.Clifford+CS.Five.D.D012 using (lem-sym12-at01103443)
open import Examples.Groups.Clifford+CS.Five.D.D080 using (lem-Cz-beta-at0110 ; lem-Cz-beta-at021021 ; lem-auto-CS01-∣-TOFF234-at243243 ; lem-auto-CX01-∣-TOFF234)
open import Examples.Groups.Clifford+CS.Five.D.D137 using (lem-auto-CCZ012-∣-CCZ342)
open import Examples.Groups.Clifford+CS.Five.D.D143 using (lem-auto-CCZ012-∣-CCZ342-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D169 using (lem-T312-beta-at0112233440 ; lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨1·0423⟩-at2442 ; lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨1·0423⟩-at2442 ; lem-sym23-at0112203443 ; lem-sym23-at0112233440 ; lem-sym23-at0112243043 ; lem-sym23-at01122440 ; lem-sym34-at0112243043 ; lem-sym34-at01122440)
open import Examples.Groups.Clifford+CS.Five.D.D183 using (lem-auto-CCZ012-∣-BOX⟨1·0324⟩)
open import Examples.Groups.Clifford+CS.Five.D.D222 using (lem-BOXd-BOX-at0110 ; lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS21-at2332 ; lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS31-at2332 ; lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS41-at2332)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-CCZ023 ; lem-nat-1-CCZ024 ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ013 ; lem-nat-2-CCZ024 ; lem-nat-2-CCZ034 ; lem-nat-2-TOFF102 ; lem-nat-2-TOFF103 ; lem-nat-2-TOFF301 ; lem-nat-3-CCZ014)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-1-CCZ013 ; lem-nat-1-CCZ014 ; lem-nat-2-TOFF201 ; lem-nat-3-CCZ013)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-CCZ024 ; lem-nat-0-CCZ124 ; lem-nat-2-CCZ124 ; lem-nat-2-CCZ134)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-0-CCZ034 ; lem-nat-0-CCZ134 ; lem-nat-0-TOFF403)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-0-TOFF413 ; lem-nat-1-TOFF013 ; lem-nat-1-TOFF401 ; lem-nat-2-TOFF402 ; lem-nat-3-TOFF301)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-1-TOFF023 ; lem-nat-3-BOX⟨0·1234⟩)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-nat-0-BOX⟨0·2134⟩ ; lem-nat-2-BOX⟨0·1243⟩)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-nat-0-BOX⟨1·2043⟩)
open import Examples.Groups.Clifford+CS.Five.D.R013 using (lem-nat-1-BOXd⟨0·2134⟩ ; lem-nat-2-TOFF403)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-0-BOX⟨0·1342⟩)
open import Examples.Groups.Clifford+CS.Five.D.R016 using (lem-nat-1-BOX⟨1·0342⟩)
open import Examples.Groups.Clifford+CS.Five.D.R017 using (lem-nat-1-TOFF402 ; lem-nat-2-BOX⟨1·0234⟩ ; lem-nat-3-TOFF401)
open import Examples.Groups.Clifford+CS.Five.D.R019 using (lem-nat-0-BOX⟨0·3124⟩ ; lem-nat-1-BOX⟨1·3024⟩)
open import Examples.Groups.Clifford+CS.Five.D.R022 using (lem-nat-1-SBOXd⟨1·0·42·3⟩ ; lem-nat-2-BOXd⟨1·0243⟩ ; lem-nat-2-BOXd⟨1·0342⟩ ; lem-nat-2-SBOXd⟨1·0·43·2⟩ ; lem-nat-3-SBOXd⟨1·0·34·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R024 using (lem-nat-0-SBOXd⟨0·2·4·3⟩ ; lem-nat-0-SBOXd⟨1·2·4·3⟩ ; lem-nat-1-SBOXd⟨0·1·4·3⟩ ; lem-nat-1-SBOXd⟨0·2·4·3⟩)
open import Examples.Groups.Clifford+CS.Five.D.R025 using (lem-nat-3-BOX⟨1·0243⟩)
open import Examples.Groups.Clifford+CS.Five.D.R026 using (lem-nat-3-BOX⟨1·0234⟩)
open import Examples.Groups.Clifford+CS.Five.D.R028 using (lem-nat-2-BOX⟨1·0324⟩)
open import Examples.Groups.Clifford+CS.Five.D.R034 using (lem-nat-1-SBOXd⟨1·3·4·2⟩ ; lem-nat-1-SBOXd⟨2·3·4·1⟩ ; lem-nat-2-SBOXd⟨1·2·4·3⟩ ; lem-nat-2-SBOXd⟨1·3·4·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R042 using (lem-comm-TOFF013-CX42 ; lem-nat-0-BOXd⟨0·2134⟩ ; lem-nat-0-BOXd⟨1·2034⟩ ; lem-nat-0-BOXd⟨1·3024⟩ ; lem-nat-1-BOXd⟨0·1234⟩ ; lem-nat-1-BOXd⟨1·3024⟩ ; lem-nat-1-BOXd⟨2·0341⟩ ; lem-nat-1-BOXd⟨2·3014⟩ ; lem-nat-1-SBOXd⟨2·0·34·1⟩ ; lem-nat-1-SBOXd⟨3·0·41·2⟩ ; lem-nat-2-BOXd⟨1·2034⟩ ; lem-nat-2-BOXd⟨1·3024⟩ ; lem-nat-2-SBOXd⟨3·0·42·1⟩ ; lem-nat-3-BOXd⟨1·0234⟩ ; lem-nat-3-BOXd⟨1·0243⟩ ; lem-nat-3-BOXd⟨2·3014⟩ ; lem-nat-3-BOXd⟨2·4013⟩ ; lem-nat-3-SBOXd⟨2·0·43·1⟩)
open import Examples.Groups.Clifford+CS.Five.D.R043 using (lem-nat-0-BOXd⟨1·0342⟩ ; lem-nat-2-BOXd⟨0·1342⟩ ; lem-nat-3-BOXd⟨0·1243⟩)
-- auto SBOXd(0;1;23;4) | CCZ132: 44 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ132 : Complete 4 → ⟪ (Sb⁻0-1-23-4 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ132 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (run b5)))))
  where
  b0 : Chain (Sb⁻0-1-23-4 ∷ CCZ123 ∷ []) (CS12 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ Toff423 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CS02 ∷ CS13 ∷ [])
  b0 = at 1 1 (CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CS13 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻0-1-32-4 ∷ []) (lem-SBsymd-at0113203442 c4) ▸
       at 0 2 (CS12 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS31-at2332 c4) ▸
       at 1 1 (Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ Toff423 ∷ Bx⁻0-1324 ∷ []) (refl) ▸
       at 5 1 (Bx0-1324 ∷ []) (lem-BOXd-BOX-at2332 c4) ▸
       at 5 1 (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-beta-T-at2332 c4) ▸
       at 8 1 (CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ []) (pw1 c4 (CCZ024 ∷ []) (CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 12 4 (CX32 ∷ CS12⁻ ∷ CX32 ∷ CS02 ∷ []) (lw4 c4 (CS02 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ []) (CX32 ∷ CS12⁻ ∷ CX32 ∷ CS02 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CS12 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ Toff423 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CS02 ∷ CS13 ∷ []) (CS12 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ Toff423 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ CS13 ∷ [])
  b1 = at 11 4 (CX32 ∷ CS12⁻ ∷ CX32 ∷ CX24 ∷ []) (lw0 c4 (CX24 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ []) (CX32 ∷ CS12⁻ ∷ CX32 ∷ CX24 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (CX32 ∷ CS04⁻ ∷ []) (pw1 c4 (CS04⁻ ∷ CX32 ∷ []) (CX32 ∷ CS04⁻ ∷ []) tt tt Eq.refl) ▸
       at 11 2 (CS12⁻ ∷ CS04⁻ ∷ []) (pw3 c4 (CS04⁻ ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CS04⁻ ∷ []) tt tt Eq.refl) ▸
       at 12 2 (CX32 ∷ CS04⁻ ∷ []) (pw1 c4 (CS04⁻ ∷ CX32 ∷ []) (CX32 ∷ CS04⁻ ∷ []) tt tt Eq.refl) ▸
       at 9 4 (CX32 ∷ CS12⁻ ∷ CX32 ∷ CX24 ∷ []) (lw0 c4 (CX24 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ []) (CX32 ∷ CS12⁻ ∷ CX32 ∷ CX24 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CX32 ∷ CS04 ∷ []) (pw1 c4 (CS04 ∷ CX32 ∷ []) (CX32 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CS12⁻ ∷ CS04 ∷ []) (pw3 c4 (CS04 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (CX32 ∷ CS04 ∷ []) (pw1 c4 (CS04 ∷ CX32 ∷ []) (CX32 ∷ CS04 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (CS12 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ Toff423 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ CS13 ∷ []) (CS12 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ Toff423 ∷ Toff013 ∷ CS04 ∷ CX24 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ Toff013 ∷ CCZ024 ∷ CS13 ∷ [])
  b2 = at 11 5 (CCZ024 ∷ []) (pw1 c4 (CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 7 4 (CX32 ∷ CS12⁻ ∷ CX32 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ []) (CX32 ∷ CS12⁻ ∷ CX32 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ []) (pw1 c4 (CCZ024 ∷ []) (CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 10 4 (CX32 ∷ CS12⁻ ∷ CX32 ∷ CS02 ∷ []) (lw4 c4 (CS02 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ []) (CX32 ∷ CS12⁻ ∷ CX32 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 9 4 (CX32 ∷ CS12⁻ ∷ CX32 ∷ CX24 ∷ []) (lw0 c4 (CX24 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ []) (CX32 ∷ CS12⁻ ∷ CX32 ∷ CX24 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CX32 ∷ CS04⁻ ∷ []) (pw1 c4 (CS04⁻ ∷ CX32 ∷ []) (CX32 ∷ CS04⁻ ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CS12⁻ ∷ CS04⁻ ∷ []) (pw3 c4 (CS04⁻ ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CS04⁻ ∷ []) tt tt Eq.refl) ▸
       at 10 2 (CX32 ∷ CS04⁻ ∷ []) (pw1 c4 (CS04⁻ ∷ CX32 ∷ []) (CX32 ∷ CS04⁻ ∷ []) tt tt Eq.refl) ▸ done

  b3 : Chain (CS12 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ Toff423 ∷ Toff013 ∷ CS04 ∷ CX24 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ Toff013 ∷ CCZ024 ∷ CS13 ∷ []) (CS12 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ Toff423 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ Bx⁻0-1324 ∷ CS13 ∷ [])
  b3 = at 7 4 (CX32 ∷ CS12⁻ ∷ CX32 ∷ CX24 ∷ []) (lw0 c4 (CX24 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ []) (CX32 ∷ CS12⁻ ∷ CX32 ∷ CX24 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CX32 ∷ CS04 ∷ []) (pw1 c4 (CS04 ∷ CX32 ∷ []) (CX32 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CS12⁻ ∷ CS04 ∷ []) (pw3 c4 (CS04 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CX32 ∷ CS04 ∷ []) (pw1 c4 (CS04 ∷ CX32 ∷ []) (CX32 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 9 5 (CCZ024 ∷ []) (pw1 c4 (CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 5 4 (CX32 ∷ CS12⁻ ∷ CX32 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ []) (CX32 ∷ CS12⁻ ∷ CX32 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 8 4 (Bx0-1324 ∷ []) (sym (lem-beta-T-at2332 c4)) ▸
       at 8 1 (Bx⁻0-1324 ∷ []) (sym (lem-BOXd-BOX-at2332 c4)) ▸ done

  b4 : Chain (CS12 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ Toff423 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ Bx⁻0-1324 ∷ CS13 ∷ []) (CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ Toff423 ∷ Bx⁻0-1324 ∷ CS13 ∷ [])
  b4 = at 4 4 (CX32 ∷ CS12⁻ ∷ CX32 ∷ Toff423 ∷ []) (lw0 c4 (Toff423 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ []) (CX32 ∷ CS12⁻ ∷ CX32 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CS14⁻ ∷ []) (refl) ▸
       at 3 4 (CX32 ∷ CS12⁻ ∷ CX32 ∷ CS14⁻ ∷ []) (lw0 c4 (CS14⁻ ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ []) (CX32 ∷ CS12⁻ ∷ CX32 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sb⁻0-1-4-2 ∷ []) (refl) ▸
       at 2 4 (CX32 ∷ CS12⁻ ∷ CX32 ∷ Toff423 ∷ []) (lw0 c4 (Toff423 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ []) (CX32 ∷ CS12⁻ ∷ CX32 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (CS14 ∷ []) (refl) ▸
       at 1 4 (CX32 ∷ CS12⁻ ∷ CX32 ∷ CS14 ∷ []) (lw0 c4 (CS14 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ []) (CX32 ∷ CS12⁻ ∷ CX32 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb0-1-4-2 ∷ []) (refl) ▸ done

  b5 : Chain (CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ Toff423 ∷ Bx⁻0-1324 ∷ CS13 ∷ []) (CCZ123 ∷ Sb⁻0-1-23-4 ∷ [])
  b5 = at 4 5 (Sb⁻0-1-32-4 ∷ []) (refl) ▸
       at 4 2 (CS13 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS21-at2332 c4) ▸
       at 5 1 (Sb⁻0-1-23-4 ∷ []) (sym (lem-SBsymd-at0113203442 c4)) ▸
       at 0 5 (CCZ123 ∷ []) (lw4 c4 (CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CS13 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | CCZ142: 26 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ142 : Complete 4 → ⟪ (Sb⁻0-1-23-4 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ142 c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Sb⁻0-1-23-4 ∷ CCZ124 ∷ []) (CS12 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ Toff423 ∷ Toff013 ∷ CCZ024 ∷ CX42 ∷ Toff013 ∷ CS12⁻ ∷ CX42 ∷ CCZ024 ∷ CS14 ∷ [])
  b0 = at 1 1 (CS12 ∷ CX42 ∷ CS12⁻ ∷ CX42 ∷ CS14 ∷ []) (lw0 c4 (CCZ124 ∷ []) (CS12 ∷ CX42 ∷ CS12⁻ ∷ CX42 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻0-1-32-4 ∷ []) (lem-SBsymd-at0113203442 c4) ▸
       at 0 2 (CS12 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS31-at2332 c4) ▸
       at 1 1 (Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ Toff423 ∷ Bx⁻0-1324 ∷ []) (refl) ▸
       at 5 1 (Bx0-1324 ∷ []) (lem-BOXd-BOX-at2332 c4) ▸
       at 5 1 (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-beta-T-at2332 c4) ▸
       at 8 4 (CX42 ∷ CS12⁻ ∷ CX42 ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ CX42 ∷ CS12⁻ ∷ CX42 ∷ []) (CX42 ∷ CS12⁻ ∷ CX42 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CX42 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX42 c4) ▸ done

  b1 : Chain (CS12 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ Toff423 ∷ Toff013 ∷ CCZ024 ∷ CX42 ∷ Toff013 ∷ CS12⁻ ∷ CX42 ∷ CCZ024 ∷ CS14 ∷ []) (CS12 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ Toff423 ∷ CX42 ∷ CS12⁻ ∷ CX42 ∷ Bx⁻0-1324 ∷ CS14 ∷ [])
  b1 = at 8 2 (CS12⁻ ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CX42 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX42 c4) ▸
       at 6 4 (CX42 ∷ CS12⁻ ∷ CX42 ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ CX42 ∷ CS12⁻ ∷ CX42 ∷ []) (CX42 ∷ CS12⁻ ∷ CX42 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CX42 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX42 c4) ▸
       at 6 2 (CS12⁻ ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CX42 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX42 c4) ▸
       at 8 4 (Bx0-1324 ∷ []) (sym (lem-beta-T-at2332 c4)) ▸
       at 8 1 (Bx⁻0-1324 ∷ []) (sym (lem-BOXd-BOX-at2332 c4)) ▸ done

  b2 : Chain (CS12 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ Toff423 ∷ CX42 ∷ CS12⁻ ∷ CX42 ∷ Bx⁻0-1324 ∷ CS14 ∷ []) (CS12 ∷ CX42 ∷ CS12⁻ ∷ CX42 ∷ CS14 ∷ Sb⁻0-1-32-4 ∷ [])
  b2 = at 3 1 (CS14⁻ ∷ []) (refl) ▸
       at 2 6 (CX42 ∷ CS12⁻ ∷ CX42 ∷ Toff423 ∷ CS14⁻ ∷ Toff423 ∷ []) (lw0 c4 (Toff423 ∷ CS14⁻ ∷ Toff423 ∷ CX42 ∷ CS12⁻ ∷ CX42 ∷ []) (CX42 ∷ CS12⁻ ∷ CX42 ∷ Toff423 ∷ CS14⁻ ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sb⁻0-1-4-2 ∷ []) (refl) ▸
       at 1 1 (CS14 ∷ []) (refl) ▸
       at 1 4 (CX42 ∷ CS12⁻ ∷ CX42 ∷ CS14 ∷ []) (lw0 c4 (CS14 ∷ CX42 ∷ CS12⁻ ∷ CX42 ∷ []) (CX42 ∷ CS12⁻ ∷ CX42 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb0-1-4-2 ∷ []) (refl) ▸
       at 4 5 (Sb⁻0-1-32-4 ∷ []) (refl) ▸
       at 4 2 (CS14 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS41-at2332 c4) ▸ done

  b3 : Chain (CS12 ∷ CX42 ∷ CS12⁻ ∷ CX42 ∷ CS14 ∷ Sb⁻0-1-32-4 ∷ []) (CCZ124 ∷ Sb⁻0-1-23-4 ∷ [])
  b3 = at 5 1 (Sb⁻0-1-23-4 ∷ []) (sym (lem-SBsymd-at0113203442 c4)) ▸
       at 0 5 (CCZ124 ∷ []) (lw0 c4 (CS12 ∷ CX42 ∷ CS12⁻ ∷ CX42 ∷ CS14 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸ done


-- auto BOXd(0;1234) | CCZ102: 5 steps
lem-auto-BOXd⟨0·1234⟩-∣-CCZ102 : Complete 4 → ⟪ (Bx⁻0-1234 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Bx⁻0-1234 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CCZ102 c4 = run b0
  where
  b0 : Chain (Bx⁻0-1234 ∷ CCZ012 ∷ []) (CCZ012 ∷ Bx⁻0-1234 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ []) (lem-BOXd-BOX c4) ▸
       at 1 1 (CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (CCZ012 ∷ Bx0-1234 ∷ []) (sym (lem-Cz-beta c4)) ▸
       at 0 1 (CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx⁻0-1234 ∷ []) (sym (lem-BOXd-BOX c4)) ▸ done


-- auto BOXd(0;1234) | CCZ103: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-CCZ103 : Complete 4 → ⟪ (Bx⁻0-1234 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Bx⁻0-1234 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CCZ103 c4 = run b0
  where
  b0 : Chain (Bx⁻0-1234 ∷ CCZ013 ∷ []) (CCZ013 ∷ Bx⁻0-1234 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ []) (lem-BOXd-BOX c4) ▸
       at 1 1 (CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 0 2 (CCZ013 ∷ Bx0-1324 ∷ []) (sym (lem-Cz-beta-at2332 c4)) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸
       at 0 1 (CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx⁻0-1234 ∷ []) (sym (lem-BOXd-BOX c4)) ▸ done


-- auto BOXd(0;1234) | CCZ124: 3 steps
lem-auto-BOXd⟨0·1234⟩-∣-CCZ124 : Complete 4 → ⟪ (Bx⁻0-1234 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Bx⁻0-1234 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CCZ124 c4 = run b0
  where
  b0 : Chain (Bx⁻0-1234 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx⁻0-1234 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ []) (lem-BOXd-BOX c4) ▸
       at 0 2 (CCZ124 ∷ Bx0-1234 ∷ []) (sym (lem-c124-beta c4)) ▸
       at 1 1 (Bx⁻0-1234 ∷ []) (sym (lem-BOXd-BOX c4)) ▸ done


-- auto BOXd(0;1234) | CCZ123: 5 steps
lem-auto-BOXd⟨0·1234⟩-∣-CCZ123 : Complete 4 → ⟪ (Bx⁻0-1234 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Bx⁻0-1234 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CCZ123 c4 = run b0
  where
  b0 : Chain (Bx⁻0-1234 ∷ CCZ123 ∷ []) (CCZ123 ∷ Bx⁻0-1234 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ []) (lem-BOXd-BOX c4) ▸
       at 0 1 (Bx0-1243 ∷ []) (lem-sym34 c4) ▸
       at 0 2 (CCZ123 ∷ Bx0-1243 ∷ []) (sym (lem-c124-beta-at3443 c4)) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym34-at3443 c4) ▸
       at 1 1 (Bx⁻0-1234 ∷ []) (sym (lem-BOXd-BOX c4)) ▸ done


-- auto BOXd(0;1234) | CCZ143: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-CCZ143 : Complete 4 → ⟪ (Bx⁻0-1234 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Bx⁻0-1234 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CCZ143 c4 = run b0
  where
  b0 : Chain (Bx⁻0-1234 ∷ CCZ134 ∷ []) (CCZ134 ∷ Bx⁻0-1234 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ []) (lem-BOXd-BOX c4) ▸
       at 1 1 (CCZ134 ∷ []) (lw0 c4 (CCZ134 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 0 2 (CCZ134 ∷ Bx0-1324 ∷ []) (sym (lem-c124-beta-at2332 c4)) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸
       at 0 1 (CCZ134 ∷ []) (lw0 c4 (CCZ134 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx⁻0-1234 ∷ []) (sym (lem-BOXd-BOX c4)) ▸ done


-- auto CCZ012 | BOX(1;0234): 3 steps
lem-auto-CCZ012-∣-BOX⟨1·0234⟩ : Complete 4 → ⟪ (CCZ012 ∷ Bx1-0234 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0234 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨1·0234⟩ c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Bx1-0234 ∷ []) (Bx1-0234 ∷ CCZ012 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Bx1-0234 ∷ CCZ012 ∷ []) (lem-Cz-beta-at0110 c4) ▸
       at 1 1 (CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸ done


-- auto CCZ012 | BOX(1;0342): 7 steps
lem-auto-CCZ012-∣-BOX⟨1·0342⟩ : Complete 4 → ⟪ (CCZ012 ∷ Bx1-0342 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0342 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨1·0342⟩ c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Bx1-0342 ∷ []) (Bx1-0342 ∷ CCZ012 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx1-0324 ∷ []) (lem-sym34-at0110233442 c4) ▸
       at 1 1 (Bx1-0234 ∷ []) (lem-sym23-at01102332 c4) ▸
       at 0 2 (Bx1-0234 ∷ CCZ012 ∷ []) (lem-Cz-beta-at0110 c4) ▸
       at 0 1 (Bx1-0324 ∷ []) (lem-sym23-at0110 c4) ▸
       at 0 1 (Bx1-0342 ∷ []) (lem-sym34-at01102332 c4) ▸
       at 1 1 (CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸ done


-- auto CCZ012 | TOFF301 CCZ342: 2 steps
lem-auto-CCZ012-∣-TOFF301-CCZ342 : Complete 4 → ⟪ (CCZ012 ∷ Toff301 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CCZ234 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-TOFF301-CCZ342 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Toff301 ∷ CCZ234 ∷ []) (Toff301 ∷ CCZ234 ∷ CCZ012 ∷ [])
  b0 = at 0 2 (Toff301 ∷ CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ Toff301 ∷ []) (Toff301 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ234 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-CCZ342 c4) ▸ done


-- auto CCZ012 | BOX(1;0324) @2332: 7 steps
lem-auto-CCZ012-∣-BOX⟨1·0324⟩-at2332 : Complete 4 → ⟪ (CCZ013 ∷ Bx1-0234 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0234 ∷ CCZ013 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨1·0324⟩-at2332 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ Bx1-0234 ∷ []) (Bx1-0234 ∷ CCZ013 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 2 2 (Bx1-0324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0234⟩ c4) ▸
       at 1 2 (Bx1-0324 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-BOX⟨1·0324⟩ c4) ▸
       at 0 2 (Bx1-0234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0324⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | BOX(1;0324) @243243: 7 steps
lem-auto-CCZ012-∣-BOX⟨1·0324⟩-at243243 : Complete 4 → ⟪ (CCZ014 ∷ Bx1-0243 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0243 ∷ CCZ014 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨1·0324⟩-at243243 c4 = run b0
  where
  b0 : Chain (CCZ014 ∷ Bx1-0243 ∷ []) (Bx1-0243 ∷ CCZ014 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 2 2 (Bx1-0234 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·0243⟩ c4) ▸
       at 1 2 (Bx1-0234 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-BOX⟨1·0324⟩-at2332 c4) ▸
       at 0 2 (Bx1-0243 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·0234⟩ c4) ▸
       at 1 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym34 @0112203443: 5 steps
lem-sym34-at0112203443 : Complete 4 → ⟪ (Bx1-2043 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2034 ∷ []) ⟫ʷ
lem-sym34-at0112203443 c4 = run b0
  where
  b0 : Chain (Bx1-2043 ∷ []) (Bx1-2034 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-2143 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2043⟩ c4) ▸
       at 1 1 (Bx0-2134 ∷ []) (lem-sym34-at12213443 c4) ▸
       at 0 2 (Bx1-2034 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2134⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | TOFF301 CCZ342 @2332: 9 steps
lem-auto-CCZ012-∣-TOFF301-CCZ342-at2332 : Complete 4 → ⟪ (CCZ013 ∷ Toff201 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CCZ234 ∷ CCZ013 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-TOFF301-CCZ342-at2332 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ013 ∷ Toff201 ∷ CCZ234 ∷ []) (Toff201 ∷ CCZ234 ∷ CCZ013 ∷ Sw23 ∷ Sw23 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 2 2 (Toff301 ∷ Sw23 ∷ []) (lem-nat-2-TOFF201 c4) ▸
       at 3 2 (CCZ234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Toff301 ∷ CCZ234 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-TOFF301-CCZ342 c4) ▸
       at 0 2 (Toff201 ∷ Sw23 ∷ []) (lem-nat-2-TOFF301 c4) ▸
       at 1 2 (CCZ234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸ done

  b1 : Chain (Toff201 ∷ CCZ234 ∷ CCZ013 ∷ Sw23 ∷ Sw23 ∷ []) (Toff201 ∷ CCZ234 ∷ CCZ013 ∷ [])
  b1 = at 3 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | TOFF301 CCZ342 @243243: 9 steps
lem-auto-CCZ012-∣-TOFF301-CCZ342-at243243 : Complete 4 → ⟪ (CCZ014 ∷ Toff201 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CCZ234 ∷ CCZ014 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-TOFF301-CCZ342-at243243 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ014 ∷ Toff201 ∷ CCZ234 ∷ []) (Toff201 ∷ CCZ234 ∷ CCZ014 ∷ Sw34 ∷ Sw34 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 2 2 (Toff201 ∷ Sw34 ∷ []) (sym (c₃ (Toffᵗ) (Swap))) ▸
       at 3 2 (CCZ234 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Toff201 ∷ CCZ234 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-TOFF301-CCZ342-at2332 c4) ▸
       at 0 2 (Toff201 ∷ Sw34 ∷ []) (sym (c₃ (Toffᵗ) (Swap))) ▸
       at 1 2 (CCZ234 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸ done

  b1 : Chain (Toff201 ∷ CCZ234 ∷ CCZ014 ∷ Sw34 ∷ Sw34 ∷ []) (Toff201 ∷ CCZ234 ∷ CCZ014 ∷ [])
  b1 = at 3 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | TOFF301 CCZ342 @12243143: 9 steps
lem-auto-CCZ012-∣-TOFF301-CCZ342-at12243143 : Complete 4 → ⟪ (CCZ024 ∷ Toff102 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CCZ134 ∷ CCZ024 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-TOFF301-CCZ342-at12243143 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ024 ∷ Toff102 ∷ CCZ134 ∷ []) (Toff102 ∷ CCZ134 ∷ CCZ024 ∷ Sw12 ∷ Sw12 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 2 2 (Toff201 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff102 ∷ []) (Toff201 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ134 ∷ []) (CCZ234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Toff201 ∷ CCZ234 ∷ CCZ014 ∷ []) (lem-auto-CCZ012-∣-TOFF301-CCZ342-at243243 c4) ▸
       at 0 2 (Toff102 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff201 ∷ []) (Toff102 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸ done

  b1 : Chain (Toff102 ∷ CCZ134 ∷ CCZ024 ∷ Sw12 ∷ Sw12 ∷ []) (Toff102 ∷ CCZ134 ∷ CCZ024 ∷ [])
  b1 = at 3 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | TOFF301 CCZ342 @13243142: 9 steps
lem-auto-CCZ012-∣-TOFF301-CCZ342-at13243142 : Complete 4 → ⟪ (CCZ034 ∷ Toff103 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ CCZ124 ∷ CCZ034 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-TOFF301-CCZ342-at13243142 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ034 ∷ Toff103 ∷ CCZ124 ∷ []) (Toff103 ∷ CCZ124 ∷ CCZ034 ∷ Sw23 ∷ Sw23 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 2 2 (Toff102 ∷ Sw23 ∷ []) (lem-nat-2-TOFF103 c4) ▸
       at 3 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 1 3 (Toff102 ∷ CCZ134 ∷ CCZ024 ∷ []) (lem-auto-CCZ012-∣-TOFF301-CCZ342-at12243143 c4) ▸
       at 0 2 (Toff103 ∷ Sw23 ∷ []) (lem-nat-2-TOFF102 c4) ▸
       at 1 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 2 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸ done

  b1 : Chain (Toff103 ∷ CCZ124 ∷ CCZ034 ∷ Sw23 ∷ Sw23 ∷ []) (Toff103 ∷ CCZ124 ∷ CCZ034 ∷ [])
  b1 = at 3 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | TOFF301 CCZ342 @0113243042: 9 steps
lem-auto-CCZ012-∣-TOFF301-CCZ342-at0113243042 : Complete 4 → ⟪ (CCZ134 ∷ Toff013 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CCZ024 ∷ CCZ134 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-TOFF301-CCZ342-at0113243042 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ134 ∷ Toff013 ∷ CCZ024 ∷ []) (Toff013 ∷ CCZ024 ∷ CCZ134 ∷ Sw01 ∷ Sw01 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 2 2 (Toff103 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff013 ∷ []) (Toff103 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 1 3 (Toff103 ∷ CCZ124 ∷ CCZ034 ∷ []) (lem-auto-CCZ012-∣-TOFF301-CCZ342-at13243142 c4) ▸
       at 0 2 (Toff013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff103 ∷ []) (Toff013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 2 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸ done

  b1 : Chain (Toff013 ∷ CCZ024 ∷ CCZ134 ∷ Sw01 ∷ Sw01 ∷ []) (Toff013 ∷ CCZ024 ∷ CCZ134 ∷ [])
  b1 = at 3 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | TOFF301 CCZ342 @0213243041: 9 steps
lem-auto-CCZ012-∣-TOFF301-CCZ342-at0213243041 : Complete 4 → ⟪ (CCZ234 ∷ Toff023 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CCZ014 ∷ CCZ234 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-TOFF301-CCZ342-at0213243041 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ234 ∷ Toff023 ∷ CCZ014 ∷ []) (Toff023 ∷ CCZ014 ∷ CCZ234 ∷ Sw12 ∷ Sw12 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff013 ∷ Sw12 ∷ []) (lem-nat-1-TOFF023 c4) ▸
       at 3 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 1 3 (Toff013 ∷ CCZ024 ∷ CCZ134 ∷ []) (lem-auto-CCZ012-∣-TOFF301-CCZ342-at0113243042 c4) ▸
       at 0 2 (Toff023 ∷ Sw12 ∷ []) (lem-nat-1-TOFF013 c4) ▸
       at 1 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 2 2 (CCZ234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ134 ∷ []) (CCZ234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Toff023 ∷ CCZ014 ∷ CCZ234 ∷ Sw12 ∷ Sw12 ∷ []) (Toff023 ∷ CCZ014 ∷ CCZ234 ∷ [])
  b1 = at 3 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | CCZ342 @12243143: 7 steps
lem-auto-CCZ012-∣-CCZ342-at12243143 : Complete 4 → ⟪ (CCZ024 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CCZ024 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ342-at12243143 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ024 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 2 2 (CCZ234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ134 ∷ []) (CCZ234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ234 ∷ CCZ014 ∷ []) (lem-auto-CCZ012-∣-CCZ342-at243243 c4) ▸
       at 0 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | CCZ342 @13243142: 7 steps
lem-auto-CCZ012-∣-CCZ342-at13243142 : Complete 4 → ⟪ (CCZ034 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CCZ034 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ342-at13243142 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ034 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 2 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 1 2 (CCZ134 ∷ CCZ024 ∷ []) (lem-auto-CCZ012-∣-CCZ342-at12243143 c4) ▸
       at 0 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 1 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | CCZ342 @0113243042: 7 steps
lem-auto-CCZ012-∣-CCZ342-at0113243042 : Complete 4 → ⟪ (CCZ134 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ CCZ134 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ342-at0113243042 c4 = run b0
  where
  b0 : Chain (CCZ134 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ134 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 2 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 1 2 (CCZ124 ∷ CCZ034 ∷ []) (lem-auto-CCZ012-∣-CCZ342-at13243142 c4) ▸
       at 0 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 1 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | CCZ342 @0213243041: 7 steps
lem-auto-CCZ012-∣-CCZ342-at0213243041 : Complete 4 → ⟪ (CCZ234 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ CCZ234 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ342-at0213243041 c4 = run b0
  where
  b0 : Chain (CCZ234 ∷ CCZ014 ∷ []) (CCZ014 ∷ CCZ234 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 1 2 (CCZ024 ∷ CCZ134 ∷ []) (lem-auto-CCZ012-∣-CCZ342-at0113243042 c4) ▸
       at 0 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 1 2 (CCZ234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ134 ∷ []) (CCZ234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOXd(0;1234) | BOX(1;0243): 32 steps
lem-auto-BOXd⟨0·1234⟩-∣-BOX⟨1·0243⟩ : Complete 4 → ⟪ (Bx⁻0-1234 ∷ Bx1-0243 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0243 ∷ Bx⁻0-1234 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-BOX⟨1·0243⟩ c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Bx⁻0-1234 ∷ Bx1-0243 ∷ []) (Toff023 ∷ CCZ014 ∷ Toff023 ∷ Bx1-2034 ∷ Toff023 ∷ Toff023 ∷ CCZ014 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ []) (lem-BOXd-BOX c4) ▸
       at 0 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 0 1 (Bx0-2314 ∷ []) (lem-sym23-at1221 c4) ▸
       at 0 1 (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) (lem-beta-T-at122331 c4) ▸
       at 3 2 (Bx1-0243 ∷ CCZ014 ∷ []) (lem-auto-CCZ012-∣-BOX⟨1·0324⟩-at243243 c4) ▸
       at 4 0 (Toff023 ∷ Toff023 ∷ []) (lw4 c4 [] (Toff023 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Bx1-2043 ∷ []) (lem-sym12-at01103443 c4) ▸
       at 3 1 (Bx1-2034 ∷ []) (lem-sym34-at0112203443 c4) ▸ done

  b1 : Chain (Toff023 ∷ CCZ014 ∷ Toff023 ∷ Bx1-2034 ∷ Toff023 ∷ Toff023 ∷ CCZ014 ∷ []) (Toff023 ∷ Bx1-2043 ∷ Toff023 ∷ Toff023 ∷ CCZ014 ∷ CCZ234 ∷ Toff023 ∷ CCZ014 ∷ [])
  b1 = at 3 1 (Bx1-2304 ∷ []) (lem-sym23-at011220 c4) ▸
       at 2 3 (Bx1-2304 ∷ CCZ234 ∷ []) (lem-T312-beta-at01122330 c4) ▸
       at 2 1 (Bx1-2034 ∷ []) (lem-sym23-at01122330 c4) ▸
       at 2 1 (Bx1-2043 ∷ []) (lem-sym34-at011220 c4) ▸
       at 2 1 (Bx1-0243 ∷ []) (lem-sym12-at0112203443 c4) ▸
       at 1 2 (Bx1-0243 ∷ CCZ014 ∷ []) (lem-auto-CCZ012-∣-BOX⟨1·0324⟩-at243243 c4) ▸
       at 2 0 (Toff023 ∷ Toff023 ∷ []) (lw4 c4 [] (Toff023 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx1-2043 ∷ []) (lem-sym12-at01103443 c4) ▸ done

  b2 : Chain (Toff023 ∷ Bx1-2043 ∷ Toff023 ∷ Toff023 ∷ CCZ014 ∷ CCZ234 ∷ Toff023 ∷ CCZ014 ∷ []) (Bx1-0243 ∷ Toff023 ∷ CCZ234 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CCZ234 ∷ [])
  b2 = at 1 1 (Bx1-2034 ∷ []) (lem-sym34-at0112203443 c4) ▸
       at 1 1 (Bx1-2304 ∷ []) (lem-sym23-at011220 c4) ▸
       at 0 3 (Bx1-2304 ∷ CCZ234 ∷ []) (lem-T312-beta-at01122330 c4) ▸
       at 0 1 (Bx1-2034 ∷ []) (lem-sym23-at01122330 c4) ▸
       at 0 1 (Bx1-2043 ∷ []) (lem-sym34-at011220 c4) ▸
       at 0 1 (Bx1-0243 ∷ []) (lem-sym12-at0112203443 c4) ▸
       at 4 3 (Toff023 ∷ CCZ014 ∷ CCZ234 ∷ []) (lem-auto-CCZ012-∣-TOFF301-CCZ342-at0213243041 c4) ▸
       at 1 2 (Toff023 ∷ CCZ234 ∷ []) (pw1 c4 (CCZ234 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸ done

  b3 : Chain (Bx1-0243 ∷ Toff023 ∷ CCZ234 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CCZ234 ∷ []) (Bx1-0243 ∷ Bx⁻0-1234 ∷ [])
  b3 = at 2 2 (CCZ014 ∷ CCZ234 ∷ []) (lem-auto-CCZ012-∣-CCZ342-at0213243041 c4) ▸
       at 3 2 (Toff023 ∷ CCZ234 ∷ []) (pw1 c4 (CCZ234 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ014 ∷ CCZ234 ∷ []) (lem-auto-CCZ012-∣-CCZ342-at0213243041 c4) ▸
       at 5 2 [] (lw0 c4 (CCZ234 ∷ CCZ234 ∷ []) [] tt tt Eq.refl) ▸
       at 1 4 (Bx0-2314 ∷ []) (sym (lem-beta-T-at122331 c4)) ▸
       at 1 1 (Bx0-2134 ∷ []) (lem-sym23-at122331 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸
       at 1 1 (Bx⁻0-1234 ∷ []) (sym (lem-BOXd-BOX c4)) ▸ done


-- BOXd-BOX @01132032: 5 steps
lem-BOXd-BOX-at01132032 : Complete 4 → ⟪ (Bx⁻1-3024 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3024 ∷ []) ⟫ʷ
lem-BOXd-BOX-at01132032 c4 = run b0
  where
  b0 : Chain (Bx⁻1-3024 ∷ []) (Bx1-3024 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx⁻0-3124 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·3024⟩ c4) ▸
       at 1 1 (Bx0-3124 ∷ []) (lem-BOXd-BOX-at132132 c4) ▸
       at 0 2 (Bx1-3024 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·3124⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- BOXd-BOX @02132031: 5 steps
lem-BOXd-BOX-at02132031 : Complete 4 → ⟪ (Bx⁻2-3014 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3014 ∷ []) ⟫ʷ
lem-BOXd-BOX-at02132031 c4 = run b0
  where
  b0 : Chain (Bx⁻2-3014 ∷ []) (Bx2-3014 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx⁻1-3024 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·3014⟩ c4) ▸
       at 1 1 (Bx1-3024 ∷ []) (lem-BOXd-BOX-at01132032 c4) ▸
       at 0 2 (Bx2-3014 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·3024⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | BOXd(2;3014): 9 steps
lem-auto-CCZ012-∣-BOXd⟨2·3014⟩ : Complete 4 → ⟪ (CCZ012 ∷ Bx⁻2-3014 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-3014 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOXd⟨2·3014⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ012 ∷ Bx⁻2-3014 ∷ []) (Bx2-3014 ∷ CCZ012 ∷ [])
  b0 = at 1 1 (Bx2-3014 ∷ []) (lem-BOXd-BOX-at02132031 c4) ▸
       at 0 1 (CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx2-0314 ∷ []) (lem-sym12-at02132031 c4) ▸
       at 1 1 (Bx2-0134 ∷ []) (lem-sym23-at02102331 c4) ▸
       at 0 2 (Bx2-0134 ∷ CCZ012 ∷ []) (lem-Cz-beta-at021021 c4) ▸
       at 0 1 (Bx2-0314 ∷ []) (lem-sym23-at021021 c4) ▸
       at 0 1 (Bx2-3014 ∷ []) (lem-sym12-at02102331 c4) ▸
       at 1 1 (CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Bx2-3014 ∷ CCZ012 ∷ []) (Bx⁻2-3014 ∷ CCZ012 ∷ [])
  b1 = at 0 1 (Bx⁻2-3014 ∷ []) (sym (lem-BOXd-BOX-at02132031 c4)) ▸ done


-- auto CCZ012 | BOXd(2;3014) @3443: 7 steps
lem-auto-CCZ012-∣-BOXd⟨2·3014⟩-at3443 : Complete 4 → ⟪ (CCZ012 ∷ Bx⁻2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-4013 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOXd⟨2·3014⟩-at3443 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Bx⁻2-4013 ∷ []) (Bx⁻2-4013 ∷ CCZ012 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 2 2 (Bx⁻2-3014 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨2·4013⟩ c4) ▸
       at 1 2 (Bx⁻2-3014 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-BOXd⟨2·3014⟩ c4) ▸
       at 0 2 (Bx⁻2-4013 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨2·3014⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | TOFF301 BOXd(2;4013): 2 steps
lem-auto-CCZ012-∣-TOFF301-BOXd⟨2·4013⟩ : Complete 4 → ⟪ (CCZ012 ∷ Toff301 ∷ Bx⁻2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ Bx⁻2-4013 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-TOFF301-BOXd⟨2·4013⟩ c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Toff301 ∷ Bx⁻2-4013 ∷ []) (Toff301 ∷ Bx⁻2-4013 ∷ CCZ012 ∷ [])
  b0 = at 0 2 (Toff301 ∷ CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ Toff301 ∷ []) (Toff301 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx⁻2-4013 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-BOXd⟨2·3014⟩-at3443 c4) ▸ done


-- auto CCZ012 | SBOXd(2;3;4;1): 1 steps
lem-auto-CCZ012-∣-SBOXd⟨2·3·4·1⟩ : Complete 4 → ⟪ (CCZ012 ∷ Sb⁻2-3-4-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-3-4-1 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOXd⟨2·3·4·1⟩ c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Sb⁻2-3-4-1 ∷ []) (Sb⁻2-3-4-1 ∷ CCZ012 ∷ [])
  b0 = at 0 2 (Sb⁻2-3-4-1 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CS • CS • CS)) ▸ done


-- auto CCZ012 | TOFF301 BOXd(2;4013) @3443: 9 steps
lem-auto-CCZ012-∣-TOFF301-BOXd⟨2·4013⟩-at3443 : Complete 4 → ⟪ (CCZ012 ∷ Toff401 ∷ Bx⁻2-3014 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ Bx⁻2-3014 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-TOFF301-BOXd⟨2·4013⟩-at3443 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ012 ∷ Toff401 ∷ Bx⁻2-3014 ∷ []) (Toff401 ∷ Bx⁻2-3014 ∷ CCZ012 ∷ Sw34 ∷ Sw34 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 2 2 (Toff301 ∷ Sw34 ∷ []) (lem-nat-3-TOFF401 c4) ▸
       at 3 2 (Bx⁻2-4013 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨2·3014⟩ c4) ▸
       at 1 3 (Toff301 ∷ Bx⁻2-4013 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-TOFF301-BOXd⟨2·4013⟩ c4) ▸
       at 0 2 (Toff401 ∷ Sw34 ∷ []) (lem-nat-3-TOFF301 c4) ▸
       at 1 2 (Bx⁻2-3014 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨2·4013⟩ c4) ▸
       at 2 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸ done

  b1 : Chain (Toff401 ∷ Bx⁻2-3014 ∷ CCZ012 ∷ Sw34 ∷ Sw34 ∷ []) (Toff401 ∷ Bx⁻2-3014 ∷ CCZ012 ∷ [])
  b1 = at 3 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | TOFF301 BOXd(2;4013) @12213443: 9 steps
lem-auto-CCZ012-∣-TOFF301-BOXd⟨2·4013⟩-at12213443 : Complete 4 → ⟪ (CCZ012 ∷ Toff402 ∷ Bx⁻1-3024 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ Bx⁻1-3024 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-TOFF301-BOXd⟨2·4013⟩-at12213443 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ012 ∷ Toff402 ∷ Bx⁻1-3024 ∷ []) (Toff402 ∷ Bx⁻1-3024 ∷ CCZ012 ∷ Sw12 ∷ Sw12 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff401 ∷ Sw12 ∷ []) (lem-nat-1-TOFF402 c4) ▸
       at 3 2 (Bx⁻2-3014 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨1·3024⟩ c4) ▸
       at 1 3 (Toff401 ∷ Bx⁻2-3014 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-TOFF301-BOXd⟨2·4013⟩-at3443 c4) ▸
       at 0 2 (Toff402 ∷ Sw12 ∷ []) (lem-nat-1-TOFF401 c4) ▸
       at 1 2 (Bx⁻1-3024 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·3014⟩ c4) ▸
       at 2 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Toff402 ∷ Bx⁻1-3024 ∷ CCZ012 ∷ Sw12 ∷ Sw12 ∷ []) (Toff402 ∷ Bx⁻1-3024 ∷ CCZ012 ∷ [])
  b1 = at 3 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | TOFF301 BOXd(2;4013) @13213442: 9 steps
lem-auto-CCZ012-∣-TOFF301-BOXd⟨2·4013⟩-at13213442 : Complete 4 → ⟪ (CCZ013 ∷ Toff403 ∷ Bx⁻1-2034 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ Bx⁻1-2034 ∷ CCZ013 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-TOFF301-BOXd⟨2·4013⟩-at13213442 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ013 ∷ Toff403 ∷ Bx⁻1-2034 ∷ []) (Toff403 ∷ Bx⁻1-2034 ∷ CCZ013 ∷ Sw23 ∷ Sw23 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 2 2 (Toff402 ∷ Sw23 ∷ []) (lem-nat-2-TOFF403 c4) ▸
       at 3 2 (Bx⁻1-3024 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·2034⟩ c4) ▸
       at 1 3 (Toff402 ∷ Bx⁻1-3024 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-TOFF301-BOXd⟨2·4013⟩-at12213443 c4) ▸
       at 0 2 (Toff403 ∷ Sw23 ∷ []) (lem-nat-2-TOFF402 c4) ▸
       at 1 2 (Bx⁻1-2034 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·3024⟩ c4) ▸
       at 2 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸ done

  b1 : Chain (Toff403 ∷ Bx⁻1-2034 ∷ CCZ013 ∷ Sw23 ∷ Sw23 ∷ []) (Toff403 ∷ Bx⁻1-2034 ∷ CCZ013 ∷ [])
  b1 = at 3 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | TOFF301 BOXd(2;4013) @0113203442: 9 steps
lem-auto-CCZ012-∣-TOFF301-BOXd⟨2·4013⟩-at0113203442 : Complete 4 → ⟪ (CCZ013 ∷ Toff413 ∷ Bx⁻0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ Bx⁻0-2134 ∷ CCZ013 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-TOFF301-BOXd⟨2·4013⟩-at0113203442 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ013 ∷ Toff413 ∷ Bx⁻0-2134 ∷ []) (Toff413 ∷ Bx⁻0-2134 ∷ CCZ013 ∷ Sw01 ∷ Sw01 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff403 ∷ Sw01 ∷ []) (lem-nat-0-TOFF413 c4) ▸
       at 3 2 (Bx⁻1-2034 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨0·2134⟩ c4) ▸
       at 1 3 (Toff403 ∷ Bx⁻1-2034 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-TOFF301-BOXd⟨2·4013⟩-at13213442 c4) ▸
       at 0 2 (Toff413 ∷ Sw01 ∷ []) (lem-nat-0-TOFF403 c4) ▸
       at 1 2 (Bx⁻0-2134 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·2034⟩ c4) ▸
       at 2 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Toff413 ∷ Bx⁻0-2134 ∷ CCZ013 ∷ Sw01 ∷ Sw01 ∷ []) (Toff413 ∷ Bx⁻0-2134 ∷ CCZ013 ∷ [])
  b1 = at 3 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | TOFF301 BOXd(2;4013) @0213203441: 9 steps
lem-auto-CCZ012-∣-TOFF301-BOXd⟨2·4013⟩-at0213203441 : Complete 4 → ⟪ (CCZ023 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ Bx⁻0-1234 ∷ CCZ023 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-TOFF301-BOXd⟨2·4013⟩-at0213203441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ023 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) (Toff423 ∷ Bx⁻0-1234 ∷ CCZ023 ∷ Sw12 ∷ Sw12 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 2 2 (Toff413 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff423 ∷ []) (Toff413 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Bx⁻0-2134 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·1234⟩ c4) ▸
       at 1 3 (Toff413 ∷ Bx⁻0-2134 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-TOFF301-BOXd⟨2·4013⟩-at0113203442 c4) ▸
       at 0 2 (Toff423 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff413 ∷ []) (Toff423 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx⁻0-1234 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·2134⟩ c4) ▸
       at 2 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸ done

  b1 : Chain (Toff423 ∷ Bx⁻0-1234 ∷ CCZ023 ∷ Sw12 ∷ Sw12 ∷ []) (Toff423 ∷ Bx⁻0-1234 ∷ CCZ023 ∷ [])
  b1 = at 3 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | SBOXd(2;3;4;1) @1221: 7 steps
lem-auto-CCZ012-∣-SBOXd⟨2·3·4·1⟩-at1221 : Complete 4 → ⟪ (CCZ012 ∷ Sb⁻1-3-4-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-3-4-2 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOXd⟨2·3·4·1⟩-at1221 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Sb⁻1-3-4-2 ∷ []) (Sb⁻1-3-4-2 ∷ CCZ012 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb⁻2-3-4-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·3·4·2⟩ c4) ▸
       at 1 2 (Sb⁻2-3-4-1 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-SBOXd⟨2·3·4·1⟩ c4) ▸
       at 0 2 (Sb⁻1-3-4-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·3·4·1⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | SBOXd(2;3;4;1) @132132: 7 steps
lem-auto-CCZ012-∣-SBOXd⟨2·3·4·1⟩-at132132 : Complete 4 → ⟪ (CCZ013 ∷ Sb⁻1-2-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-2-4-3 ∷ CCZ013 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOXd⟨2·3·4·1⟩-at132132 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ Sb⁻1-2-4-3 ∷ []) (Sb⁻1-2-4-3 ∷ CCZ013 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 2 2 (Sb⁻1-3-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·2·4·3⟩ c4) ▸
       at 1 2 (Sb⁻1-3-4-2 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-SBOXd⟨2·3·4·1⟩-at1221 c4) ▸
       at 0 2 (Sb⁻1-2-4-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·3·4·2⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | SBOXd(2;3;4;1) @01132032: 7 steps
lem-auto-CCZ012-∣-SBOXd⟨2·3·4·1⟩-at01132032 : Complete 4 → ⟪ (CCZ013 ∷ Sb⁻0-2-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-2-4-3 ∷ CCZ013 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOXd⟨2·3·4·1⟩-at01132032 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ Sb⁻0-2-4-3 ∷ []) (Sb⁻0-2-4-3 ∷ CCZ013 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb⁻1-2-4-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·2·4·3⟩ c4) ▸
       at 1 2 (Sb⁻1-2-4-3 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-SBOXd⟨2·3·4·1⟩-at132132 c4) ▸
       at 0 2 (Sb⁻0-2-4-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·2·4·3⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | SBOXd(2;3;4;1) @02132031: 7 steps
lem-auto-CCZ012-∣-SBOXd⟨2·3·4·1⟩-at02132031 : Complete 4 → ⟪ (CCZ023 ∷ Sb⁻0-1-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-4-3 ∷ CCZ023 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOXd⟨2·3·4·1⟩-at02132031 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ Sb⁻0-1-4-3 ∷ []) (Sb⁻0-1-4-3 ∷ CCZ023 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 2 2 (Sb⁻0-2-4-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨0·1·4·3⟩ c4) ▸
       at 1 2 (Sb⁻0-2-4-3 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-SBOXd⟨2·3·4·1⟩-at01132032 c4) ▸
       at 0 2 (Sb⁻0-1-4-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨0·2·4·3⟩ c4) ▸
       at 1 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | BOXd(2;3014) @1221: 7 steps
lem-auto-CCZ012-∣-BOXd⟨2·3014⟩-at1221 : Complete 4 → ⟪ (CCZ012 ∷ Bx⁻1-3024 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-3024 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOXd⟨2·3014⟩-at1221 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Bx⁻1-3024 ∷ []) (Bx⁻1-3024 ∷ CCZ012 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx⁻2-3014 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨1·3024⟩ c4) ▸
       at 1 2 (Bx⁻2-3014 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-BOXd⟨2·3014⟩ c4) ▸
       at 0 2 (Bx⁻1-3024 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·3014⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | BOXd(2;3014) @132132: 7 steps
lem-auto-CCZ012-∣-BOXd⟨2·3014⟩-at132132 : Complete 4 → ⟪ (CCZ013 ∷ Bx⁻1-2034 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-2034 ∷ CCZ013 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOXd⟨2·3014⟩-at132132 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ Bx⁻1-2034 ∷ []) (Bx⁻1-2034 ∷ CCZ013 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 2 2 (Bx⁻1-3024 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·2034⟩ c4) ▸
       at 1 2 (Bx⁻1-3024 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-BOXd⟨2·3014⟩-at1221 c4) ▸
       at 0 2 (Bx⁻1-2034 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·3024⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | BOXd(2;3014) @01132032: 7 steps
lem-auto-CCZ012-∣-BOXd⟨2·3014⟩-at01132032 : Complete 4 → ⟪ (CCZ013 ∷ Bx⁻0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-2134 ∷ CCZ013 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOXd⟨2·3014⟩-at01132032 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ Bx⁻0-2134 ∷ []) (Bx⁻0-2134 ∷ CCZ013 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx⁻1-2034 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨0·2134⟩ c4) ▸
       at 1 2 (Bx⁻1-2034 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-BOXd⟨2·3014⟩-at132132 c4) ▸
       at 0 2 (Bx⁻0-2134 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·2034⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | BOXd(2;3014) @02132031: 7 steps
lem-auto-CCZ012-∣-BOXd⟨2·3014⟩-at02132031 : Complete 4 → ⟪ (CCZ023 ∷ Bx⁻0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-1234 ∷ CCZ023 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOXd⟨2·3014⟩-at02132031 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ Bx⁻0-1234 ∷ []) (Bx⁻0-1234 ∷ CCZ023 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 2 2 (Bx⁻0-2134 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·1234⟩ c4) ▸
       at 1 2 (Bx⁻0-2134 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-BOXd⟨2·3014⟩-at01132032 c4) ▸
       at 0 2 (Bx⁻0-1234 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·2134⟩ c4) ▸
       at 1 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | BOX(1;0243): 31 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-BOX⟨1·0243⟩ : Complete 4 → ⟪ (Sb⁻0-1-23-4 ∷ Bx1-0243 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0243 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-BOX⟨1·0243⟩ c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Sb⁻0-1-23-4 ∷ Bx1-0243 ∷ []) (Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Bx1-2340 ∷ CCZ023 ∷ Toff423 ∷ Bx⁻0-1234 ∷ [])
  b0 = at 0 1 (Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) (refl) ▸
       at 4 2 (Bx1-0243 ∷ Bx⁻0-1234 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-BOX⟨1·0243⟩ c4) ▸
       at 5 0 (Toff423 ∷ Toff423 ∷ []) (lw0 c4 [] (Toff423 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx1-2043 ∷ []) (lem-sym12-at01103443 c4) ▸
       at 4 1 (Bx1-2403 ∷ []) (lem-sym23-at0112203443 c4) ▸
       at 4 1 (Bx1-2430 ∷ []) (lem-sym34-at0112243043 c4) ▸
       at 4 1 (Bx1-2340 ∷ []) (lem-sym23-at01122440 c4) ▸
       at 3 3 (Bx1-2340 ∷ CCZ023 ∷ []) (lem-T312-beta-at0112233440 c4) ▸ done

  b1 : Chain (Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Bx1-2340 ∷ CCZ023 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) (Sb0-1-4-3 ∷ Toff423 ∷ Bx1-2403 ∷ Toff423 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ CCZ023 ∷ Toff423 ∷ Bx⁻0-1234 ∷ [])
  b1 = at 3 1 (Bx1-2430 ∷ []) (lem-sym23-at0112233440 c4) ▸
       at 3 1 (Bx1-2403 ∷ []) (lem-sym34-at01122440 c4) ▸
       at 3 1 (Bx1-2043 ∷ []) (lem-sym23-at0112243043 c4) ▸
       at 3 1 (Bx1-0243 ∷ []) (lem-sym12-at0112203443 c4) ▸
       at 2 2 (Bx1-0243 ∷ Sb⁻0-1-4-3 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨1·0423⟩-at2442 c4) ▸
       at 3 0 (Toff423 ∷ Toff423 ∷ []) (lw0 c4 [] (Toff423 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Bx1-2043 ∷ []) (lem-sym12-at01103443 c4) ▸
       at 2 1 (Bx1-2403 ∷ []) (lem-sym23-at0112203443 c4) ▸ done

  b2 : Chain (Sb0-1-4-3 ∷ Toff423 ∷ Bx1-2403 ∷ Toff423 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ CCZ023 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) (Bx1-0243 ∷ Sb0-1-4-3 ∷ CCZ023 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ CCZ023 ∷ Toff423 ∷ Bx⁻0-1234 ∷ [])
  b2 = at 2 1 (Bx1-2430 ∷ []) (lem-sym34-at0112243043 c4) ▸
       at 2 1 (Bx1-2340 ∷ []) (lem-sym23-at01122440 c4) ▸
       at 1 3 (Bx1-2340 ∷ CCZ023 ∷ []) (lem-T312-beta-at0112233440 c4) ▸
       at 1 1 (Bx1-2430 ∷ []) (lem-sym23-at0112233440 c4) ▸
       at 1 1 (Bx1-2403 ∷ []) (lem-sym34-at01122440 c4) ▸
       at 1 1 (Bx1-2043 ∷ []) (lem-sym23-at0112243043 c4) ▸
       at 1 1 (Bx1-0243 ∷ []) (lem-sym12-at0112203443 c4) ▸
       at 0 2 (Bx1-0243 ∷ Sb0-1-4-3 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨1·0423⟩-at2442 c4) ▸ done

  b3 : Chain (Bx1-0243 ∷ Sb0-1-4-3 ∷ CCZ023 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ CCZ023 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) (Bx1-0243 ∷ Sb⁻0-1-23-4 ∷ [])
  b3 = at 5 3 (Toff423 ∷ Bx⁻0-1234 ∷ CCZ023 ∷ []) (lem-auto-CCZ012-∣-TOFF301-BOXd⟨2·4013⟩-at0213203441 c4) ▸
       at 2 2 (Toff423 ∷ CCZ023 ∷ []) (pw1 c4 (CCZ023 ∷ Toff423 ∷ []) (Toff423 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Sb⁻0-1-4-3 ∷ CCZ023 ∷ []) (lem-auto-CCZ012-∣-SBOXd⟨2·3·4·1⟩-at02132031 c4) ▸
       at 4 2 (Toff423 ∷ CCZ023 ∷ []) (pw1 c4 (CCZ023 ∷ Toff423 ∷ []) (Toff423 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx⁻0-1234 ∷ CCZ023 ∷ []) (lem-auto-CCZ012-∣-BOXd⟨2·3014⟩-at02132031 c4) ▸
       at 6 2 [] (lw4 c4 (CCZ023 ∷ CCZ023 ∷ []) [] tt tt Eq.refl) ▸
       at 1 5 (Sb⁻0-1-23-4 ∷ []) (refl) ▸ done


-- auto CS01 | BOXd(1;0234): 7 steps
lem-auto-CS01-∣-BOXd⟨1·0234⟩ : Complete 4 → ⟪ (CS01 ∷ Bx⁻1-0234 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-0234 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOXd⟨1·0234⟩ c4 = run b0
  where
  b0 : Chain (CS01 ∷ Bx⁻1-0234 ∷ []) (Bx⁻1-0234 ∷ CS01 ∷ [])
  b0 = at 1 1 (Bx1-0234 ∷ []) (lem-BOXd-BOX-at0110 c4) ▸
       at 0 1 (CS01 ∷ []) (lw4 c4 (CS01 ∷ []) (CS01 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx1-2034 ∷ []) (lem-sym12-at0110 c4) ▸
       at 0 2 (Bx1-2034 ∷ CS01 ∷ []) (lem-CS20-beta-c-at011220 c4) ▸
       at 0 1 (Bx1-0234 ∷ []) (lem-sym12-at011220 c4) ▸
       at 1 1 (CS01 ∷ []) (lw4 c4 (CS01 ∷ []) (CS01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx⁻1-0234 ∷ []) (sym (lem-BOXd-BOX-at0110 c4)) ▸ done


-- auto CS01 | SBOXd(1;0;23;4): 11 steps
lem-auto-CS01-∣-SBOXd⟨1·0·23·4⟩ : Complete 4 → ⟪ (CS01 ∷ Sb⁻1-0-23-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-23-4 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOXd⟨1·0·23·4⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS01 ∷ Sb⁻1-0-23-4 ∷ []) (Sb1-0-4-3 ∷ Toff423 ∷ Sb⁻1-0-4-3 ∷ CS01 ∷ Toff423 ∷ Bx⁻1-0234 ∷ [])
  b0 = at 1 1 (Sb1-0-4-3 ∷ Toff423 ∷ Sb⁻1-0-4-3 ∷ Toff423 ∷ Bx⁻1-0234 ∷ []) (refl) ▸
       at 1 1 (CS04 ∷ []) (refl) ▸
       at 0 2 (CS04 ∷ CS01 ∷ []) (pw2 c4 (CS01 ∷ CS04 ∷ []) (CS04 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb1-0-4-3 ∷ []) (refl) ▸
       at 1 2 (Toff423 ∷ CS01 ∷ []) (lem-auto-CS01-∣-TOFF234-at243243 c4) ▸
       at 3 1 (CS04⁻ ∷ []) (refl) ▸
       at 2 2 (CS04⁻ ∷ CS01 ∷ []) (pw2 c4 (CS01 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb⁻1-0-4-3 ∷ []) (refl) ▸ done

  b1 : Chain (Sb1-0-4-3 ∷ Toff423 ∷ Sb⁻1-0-4-3 ∷ CS01 ∷ Toff423 ∷ Bx⁻1-0234 ∷ []) (Sb⁻1-0-23-4 ∷ CS01 ∷ [])
  b1 = at 3 2 (Toff423 ∷ CS01 ∷ []) (lem-auto-CS01-∣-TOFF234-at243243 c4) ▸
       at 4 2 (Bx⁻1-0234 ∷ CS01 ∷ []) (lem-auto-CS01-∣-BOXd⟨1·0234⟩ c4) ▸
       at 0 5 (Sb⁻1-0-23-4 ∷ []) (refl) ▸ done


-- auto CX01 | BOXd(1;0234): 3 steps
lem-auto-CX01-∣-BOXd⟨1·0234⟩ : Complete 4 → ⟪ (CX01 ∷ Bx⁻1-0234 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-0234 ∷ CX01 ∷ []) ⟫ʷ
lem-auto-CX01-∣-BOXd⟨1·0234⟩ c4 = run b0
  where
  b0 : Chain (CX01 ∷ Bx⁻1-0234 ∷ []) (Bx⁻1-0234 ∷ CX01 ∷ [])
  b0 = at 1 1 (Bx1-0234 ∷ []) (lem-BOXd-BOX-at0110 c4) ▸
       at 0 2 (Bx1-0234 ∷ CX01 ∷ []) (lem-CX10-beta-c-at0110 c4) ▸
       at 0 1 (Bx⁻1-0234 ∷ []) (sym (lem-BOXd-BOX-at0110 c4)) ▸ done


-- F0d @1221: 5 steps
lem-F0d-at1221 : Complete 4 → ⟪ (Sb⁻1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-0-42-1 ∷ []) ⟫ʷ
lem-F0d-at1221 c4 = run b0
  where
  b0 : Chain (Sb⁻1-0-42-3 ∷ []) (Sb⁻3-0-42-1 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·0·42·3⟩ c4) ▸
       at 1 1 (Sb⁻3-0-41-2 ∷ []) (lem-F0d c4) ▸
       at 0 2 (Sb⁻3-0-42-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨3·0·41·2⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- F0d @132132: 5 steps
lem-F0d-at132132 : Complete 4 → ⟪ (Sb⁻1-0-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-43-1 ∷ []) ⟫ʷ
lem-F0d-at132132 c4 = run b0
  where
  b0 : Chain (Sb⁻1-0-43-2 ∷ []) (Sb⁻2-0-43-1 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻1-0-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·43·2⟩ c4) ▸
       at 1 1 (Sb⁻3-0-42-1 ∷ []) (lem-F0d-at1221 c4) ▸
       at 0 2 (Sb⁻2-0-43-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨3·0·42·1⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- F0d @14213243: 5 steps
lem-F0d-at14213243 : Complete 4 → ⟪ (Sb⁻1-0-34-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-34-1 ∷ []) ⟫ʷ
lem-F0d-at14213243 c4 = run b0
  where
  b0 : Chain (Sb⁻1-0-34-2 ∷ []) (Sb⁻2-0-34-1 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻1-0-43-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨1·0·34·2⟩ c4) ▸
       at 1 1 (Sb⁻2-0-43-1 ∷ []) (lem-F0d-at132132 c4) ▸
       at 0 2 (Sb⁻2-0-34-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨2·0·43·1⟩ c4) ▸
       at 1 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- F0d @143143: 5 steps
lem-F0d-at143143 : Complete 4 → ⟪ (Sb⁻2-0-34-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-34-2 ∷ []) ⟫ʷ
lem-F0d-at143143 c4 = run b0
  where
  b0 : Chain (Sb⁻2-0-34-1 ∷ []) (Sb⁻1-0-34-2 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻1-0-34-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·34·1⟩ c4) ▸
       at 1 1 (Sb⁻2-0-34-1 ∷ []) (lem-F0d-at14213243 c4) ▸
       at 0 2 (Sb⁻1-0-34-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·34·1⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CX01 | BOXd(1;0234) @3443: 7 steps
lem-auto-CX01-∣-BOXd⟨1·0234⟩-at3443 : Complete 4 → ⟪ (CX01 ∷ Bx⁻1-0243 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-0243 ∷ CX01 ∷ []) ⟫ʷ
lem-auto-CX01-∣-BOXd⟨1·0234⟩-at3443 c4 = run b0
  where
  b0 : Chain (CX01 ∷ Bx⁻1-0243 ∷ []) (Bx⁻1-0243 ∷ CX01 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 2 2 (Bx⁻1-0234 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨1·0243⟩ c4) ▸
       at 1 2 (Bx⁻1-0234 ∷ CX01 ∷ []) (lem-auto-CX01-∣-BOXd⟨1·0234⟩ c4) ▸
       at 0 2 (Bx⁻1-0243 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨1·0234⟩ c4) ▸
       at 1 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CX01 | BOXd(1;0234) @233442: 7 steps
lem-auto-CX01-∣-BOXd⟨1·0234⟩-at233442 : Complete 4 → ⟪ (CX01 ∷ Bx⁻1-0342 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-0342 ∷ CX01 ∷ []) ⟫ʷ
lem-auto-CX01-∣-BOXd⟨1·0234⟩-at233442 c4 = run b0
  where
  b0 : Chain (CX01 ∷ Bx⁻1-0342 ∷ []) (Bx⁻1-0342 ∷ CX01 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 2 2 (Bx⁻1-0243 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·0342⟩ c4) ▸
       at 1 2 (Bx⁻1-0243 ∷ CX01 ∷ []) (lem-auto-CX01-∣-BOXd⟨1·0234⟩-at3443 c4) ▸
       at 0 2 (Bx⁻1-0342 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·0243⟩ c4) ▸
       at 1 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CX01 | SBOXd(2;0;34;1): 13 steps
lem-auto-CX01-∣-SBOXd⟨2·0·34·1⟩ : Complete 4 → ⟪ (CX01 ∷ Sb⁻2-0-34-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-34-1 ∷ CX01 ∷ []) ⟫ʷ
lem-auto-CX01-∣-SBOXd⟨2·0·34·1⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX01 ∷ Sb⁻2-0-34-1 ∷ []) (Sb1-0-2-4 ∷ Toff234 ∷ CS02⁻ ∷ CX01 ∷ Toff234 ∷ Bx⁻1-0342 ∷ [])
  b0 = at 1 1 (Sb⁻1-0-34-2 ∷ []) (lem-F0d-at143143 c4) ▸
       at 1 1 (Sb1-0-2-4 ∷ Toff234 ∷ Sb⁻1-0-2-4 ∷ Toff234 ∷ Bx⁻1-0342 ∷ []) (refl) ▸
       at 1 1 (CS02 ∷ []) (refl) ▸
       at 0 2 (CS02 ∷ CX01 ∷ []) (lw4 c4 (CX01 ∷ CS02 ∷ []) (CS02 ∷ CX01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb1-0-2-4 ∷ []) (refl) ▸
       at 1 2 (Toff234 ∷ CX01 ∷ []) (lem-auto-CX01-∣-TOFF234 c4) ▸
       at 3 1 (CS02⁻ ∷ []) (refl) ▸
       at 2 2 (CS02⁻ ∷ CX01 ∷ []) (lw4 c4 (CX01 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CX01 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Sb1-0-2-4 ∷ Toff234 ∷ CS02⁻ ∷ CX01 ∷ Toff234 ∷ Bx⁻1-0342 ∷ []) (Sb⁻2-0-34-1 ∷ CX01 ∷ [])
  b1 = at 2 1 (Sb⁻1-0-2-4 ∷ []) (refl) ▸
       at 3 2 (Toff234 ∷ CX01 ∷ []) (lem-auto-CX01-∣-TOFF234 c4) ▸
       at 4 2 (Bx⁻1-0342 ∷ CX01 ∷ []) (lem-auto-CX01-∣-BOXd⟨1·0234⟩-at233442 c4) ▸
       at 0 5 (Sb⁻1-0-34-2 ∷ []) (refl) ▸
       at 0 1 (Sb⁻2-0-34-1 ∷ []) (sym (lem-F0d-at143143 c4)) ▸ done


-- BOXd-BOX @3443: 5 steps
lem-BOXd-BOX-at3443 : Complete 4 → ⟪ (Bx⁻0-1243 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ []) ⟫ʷ
lem-BOXd-BOX-at3443 c4 = run b0
  where
  b0 : Chain (Bx⁻0-1243 ∷ []) (Bx0-1243 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx⁻0-1234 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·1243⟩ c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-BOXd-BOX c4) ▸
       at 0 2 (Bx0-1243 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1234⟩ c4) ▸
       at 1 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- BOXd-BOX @233442: 5 steps
lem-BOXd-BOX-at233442 : Complete 4 → ⟪ (Bx⁻0-1342 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1342 ∷ []) ⟫ʷ
lem-BOXd-BOX-at233442 c4 = run b0
  where
  b0 : Chain (Bx⁻0-1342 ∷ []) (Bx0-1342 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx⁻0-1243 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·1342⟩ c4) ▸
       at 1 1 (Bx0-1243 ∷ []) (lem-BOXd-BOX-at3443 c4) ▸
       at 0 2 (Bx0-1342 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1243⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- BOXd-BOX @0110233442: 5 steps
lem-BOXd-BOX-at0110233442 : Complete 4 → ⟪ (Bx⁻1-0342 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0342 ∷ []) ⟫ʷ
lem-BOXd-BOX-at0110233442 c4 = run b0
  where
  b0 : Chain (Bx⁻1-0342 ∷ []) (Bx1-0342 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx⁻0-1342 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·0342⟩ c4) ▸
       at 1 1 (Bx0-1342 ∷ []) (lem-BOXd-BOX-at233442 c4) ▸
       at 0 2 (Bx1-0342 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1342⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- BOXd-BOX @0210233441: 5 steps
lem-BOXd-BOX-at0210233441 : Complete 4 → ⟪ (Bx⁻2-0341 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0341 ∷ []) ⟫ʷ
lem-BOXd-BOX-at0210233441 c4 = run b0
  where
  b0 : Chain (Bx⁻2-0341 ∷ []) (Bx2-0341 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx⁻1-0342 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·0341⟩ c4) ▸
       at 1 1 (Bx1-0342 ∷ []) (lem-BOXd-BOX-at0110233442 c4) ▸
       at 0 2 (Bx2-0341 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0342⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CS01 | BOXd(2;0341): 7 steps
lem-auto-CS01-∣-BOXd⟨2·0341⟩ : Complete 4 → ⟪ (CS01 ∷ Bx⁻2-0341 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-0341 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOXd⟨2·0341⟩ c4 = run b0
  where
  b0 : Chain (CS01 ∷ Bx⁻2-0341 ∷ []) (Bx⁻2-0341 ∷ CS01 ∷ [])
  b0 = at 1 1 (Bx2-0341 ∷ []) (lem-BOXd-BOX-at0210233441 c4) ▸
       at 1 1 (Bx2-0314 ∷ []) (lem-sym34-at0210233441 c4) ▸
       at 1 1 (Bx2-0134 ∷ []) (lem-sym23-at02102331 c4) ▸
       at 0 2 (Bx2-0134 ∷ CS01 ∷ []) (lem-CS12-beta-at021021 c4) ▸
       at 0 1 (Bx2-0314 ∷ []) (lem-sym23-at021021 c4) ▸
       at 0 1 (Bx2-0341 ∷ []) (lem-sym34-at02102331 c4) ▸
       at 0 1 (Bx⁻2-0341 ∷ []) (sym (lem-BOXd-BOX-at0210233441 c4)) ▸ done


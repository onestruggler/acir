{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D009 where

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
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-BOXd-BOX ; lem-CS20-beta-c ; lem-CS20-beta-ci ; lem-CX10-beta-c ; lem-CX23-beta ; lem-CZ10-beta-c ; lem-beta-T-at2332 ; lem-c124-beta ; lem-sym12 ; lem-sym23 ; lem-sym34)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-sym12-at1221 ; lem-sym12-at132132 ; lem-sym12-at14213243)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-c124-beta-at0310213442 ; lem-c124-beta-at2332 ; lem-sym12-at233442 ; lem-sym23-at13213442 ; lem-sym23-at13243142 ; lem-sym23-at2332 ; lem-sym23-at243243 ; lem-sym23-at3443 ; lem-sym34-at13213442 ; lem-sym34-at2332 ; lem-sym34-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-BOXd-BOX-at2332 ; lem-CS20-beta-c-at1221 ; lem-sym12-at2332 ; lem-sym12-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D007 using (lem-CS12-beta-at12243143 ; lem-SBsym-at0113203442 ; lem-auto-BOX⟨0·1234⟩-∣-K0 ; lem-auto-BOX⟨0·1234⟩-∣-Kd0)
open import Examples.Groups.Clifford+CS.Five.D.D008 using (lem-SBsymd-at0113203442 ; lem-auto-BOXd⟨0·1234⟩-∣-Kd0 ; lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS10-at2332 ; lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS20-at2332 ; lem-auto-SBOXd⟨0·1·23·4⟩-∣-K0 ; lem-auto-TOFF012-∣-CS34-at0412233140)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-BOX⟨0·2134⟩ ; lem-nat-2-BOX⟨0·1234⟩ ; lem-nat-2-BOX⟨0·1324⟩ ; lem-nat-2-BOX⟨0·3412⟩ ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ013 ; lem-nat-3-BOX⟨0·1423⟩)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-2-BOX⟨0·2413⟩ ; lem-nat-3-BOX⟨0·1324⟩)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-2-BOX⟨0·3124⟩ ; lem-nat-2-CCZ124 ; lem-nat-2-CCZ134)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-3-BOX⟨0·4123⟩)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-1-BOX⟨0·1234⟩ ; lem-nat-2-BOX⟨0·2134⟩ ; lem-nat-3-BOX⟨0·3124⟩)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-2-CZ03)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-2-CZ02)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-nat-1-CX10 ; lem-nat-1-CX20 ; lem-nat-3-CZ03 ; lem-nat-3-CZ04)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-2-CS02 ; lem-nat-2-CSd02 ; lem-nat-2-SBOX⟨0·1·23·4⟩ ; lem-nat-2-SBOX⟨0·1·32·4⟩)
open import Examples.Groups.Clifford+CS.Five.D.R016 using (lem-nat-3-CS04 ; lem-nat-3-CSd04)
open import Examples.Groups.Clifford+CS.Five.D.R017 using (lem-nat-3-CS03 ; lem-nat-3-CSd03)
open import Examples.Groups.Clifford+CS.Five.D.R018 using (lem-nat-2-SBOXd⟨0·1·23·4⟩ ; lem-nat-2-SBOXd⟨0·1·32·4⟩)
open import Examples.Groups.Clifford+CS.Five.D.R019 using (lem-comm-CCZ024-CX13 ; lem-comm-CSd02-CCZ134 ; lem-nat-2-CS03 ; lem-nat-2-CSd03 ; lem-nat-2-CX12 ; lem-nat-2-CX20 ; lem-nat-2-CX30 ; lem-nat-3-CX30 ; lem-nat-3-CX40)
-- auto SBOXd(0;1;23;4) | CCZ013: 56 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ013 : Complete 4 → ⟪ (Sb⁻0-1-23-4 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ013 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (run b6))))))
  where
  b0 : Chain (Sb⁻0-1-23-4 ∷ CCZ013 ∷ []) (CS03 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ Toff423 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CX13 ∷ CS03⁻ ∷ CCZ024 ∷ CX13 ∷ CS01 ∷ [])
  b0 = at 1 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (lw4 c4 (CCZ013 ∷ []) (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻0-1-32-4 ∷ []) (lem-SBsymd-at0113203442 c4) ▸
       at 0 2 (CS03 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS20-at2332 c4) ▸
       at 1 1 (Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ Toff423 ∷ Bx⁻0-1324 ∷ []) (refl) ▸
       at 5 1 (Bx0-1324 ∷ []) (lem-BOXd-BOX-at2332 c4) ▸
       at 5 1 (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-beta-T-at2332 c4) ▸
       at 8 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 c4) ▸
       at 9 2 (CS03⁻ ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CS03 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ Toff423 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CX13 ∷ CS03⁻ ∷ CCZ024 ∷ CX13 ∷ CS01 ∷ []) (CS03 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ Toff423 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ Bx⁻0-1324 ∷ CS01 ∷ [])
  b1 = at 10 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 c4) ▸
       at 7 4 (CX13 ∷ CS03⁻ ∷ CX13 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ []) (CX13 ∷ CS03⁻ ∷ CX13 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 c4) ▸
       at 7 2 (CS03⁻ ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 c4) ▸
       at 5 4 (CX13 ∷ CS03⁻ ∷ CX13 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ []) (CX13 ∷ CS03⁻ ∷ CX13 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 8 4 (Bx0-1324 ∷ []) (sym (lem-beta-T-at2332 c4)) ▸
       at 8 1 (Bx⁻0-1324 ∷ []) (sym (lem-BOXd-BOX-at2332 c4)) ▸ done

  b2 : Chain (CS03 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ Toff423 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ Bx⁻0-1324 ∷ CS01 ∷ []) (CS03 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ K4 ∷ CS24 ∷ CX32 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ K4⁻ ∷ Bx⁻0-1324 ∷ CS01 ∷ [])
  b2 = at 4 1 (K4 ∷ CCZ234 ∷ K4⁻ ∷ []) (lw0 c4 (Toff423 ∷ []) (K4 ∷ CCZ234 ∷ K4⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 4 (CX13 ∷ CS03⁻ ∷ CX13 ∷ K4⁻ ∷ []) (pw2 c4 (K4⁻ ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ []) (CX13 ∷ CS03⁻ ∷ CX13 ∷ K4⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ []) (lw0 c4 (CCZ234 ∷ []) (CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 9 4 (CX13 ∷ CS03⁻ ∷ CX13 ∷ CS34 ∷ []) (pw2 c4 (CS34 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ []) (CX13 ∷ CS03⁻ ∷ CX13 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 8 4 (CX13 ∷ CS03⁻ ∷ CX13 ∷ CX32 ∷ []) (lw4 c4 (CX32 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ []) (CX13 ∷ CS03⁻ ∷ CX13 ∷ CX32 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CX13 ∷ CS24⁻ ∷ []) (lw0 c4 (CS24⁻ ∷ CX13 ∷ []) (CX13 ∷ CS24⁻ ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CS03⁻ ∷ CS24⁻ ∷ []) (pw1 c4 (CS24⁻ ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CS24⁻ ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CX13 ∷ CS24⁻ ∷ []) (lw0 c4 (CS24⁻ ∷ CX13 ∷ []) (CX13 ∷ CS24⁻ ∷ []) tt tt Eq.refl) ▸ done

  b3 : Chain (CS03 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ K4 ∷ CS24 ∷ CX32 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ K4⁻ ∷ Bx⁻0-1324 ∷ CS01 ∷ []) (CS03 ∷ Sb0-1-4-2 ∷ Toff423 ∷ CS14⁻ ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ Toff423 ∷ Bx⁻0-1324 ∷ CS01 ∷ [])
  b3 = at 6 4 (CX13 ∷ CS03⁻ ∷ CX13 ∷ CX32 ∷ []) (lw4 c4 (CX32 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ []) (CX13 ∷ CS03⁻ ∷ CX13 ∷ CX32 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CX13 ∷ CS24 ∷ []) (lw0 c4 (CS24 ∷ CX13 ∷ []) (CX13 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CS03⁻ ∷ CS24 ∷ []) (pw1 c4 (CS24 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CX13 ∷ CS24 ∷ []) (lw0 c4 (CS24 ∷ CX13 ∷ []) (CX13 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 8 5 (CCZ234 ∷ []) (lw0 c4 (CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 4 4 (CX13 ∷ CS03⁻ ∷ CX13 ∷ K4 ∷ []) (pw2 c4 (K4 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ []) (CX13 ∷ CS03⁻ ∷ CX13 ∷ K4 ∷ []) tt tt Eq.refl) ▸
       at 7 3 (Toff423 ∷ []) (lw0 c4 (K4 ∷ CCZ234 ∷ K4⁻ ∷ []) (Toff423 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CS14⁻ ∷ []) (refl) ▸ done

  b4 : Chain (CS03 ∷ Sb0-1-4-2 ∷ Toff423 ∷ CS14⁻ ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ Toff423 ∷ Bx⁻0-1324 ∷ CS01 ∷ []) (CS03 ∷ Sb0-1-4-2 ∷ K4 ∷ CS24 ∷ CX32 ∷ CX13 ∷ CS24⁻ ∷ CS03⁻ ∷ CX13 ∷ CX32 ∷ CS34 ∷ K4⁻ ∷ Sb⁻0-1-4-2 ∷ Toff423 ∷ Bx⁻0-1324 ∷ CS01 ∷ [])
  b4 = at 3 4 (CX13 ∷ CS03⁻ ∷ CX13 ∷ CS14⁻ ∷ []) (pw2 c4 (CS14⁻ ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ []) (CX13 ∷ CS03⁻ ∷ CX13 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sb⁻0-1-4-2 ∷ []) (refl) ▸
       at 2 1 (K4 ∷ CCZ234 ∷ K4⁻ ∷ []) (lw0 c4 (Toff423 ∷ []) (K4 ∷ CCZ234 ∷ K4⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 4 (CX13 ∷ CS03⁻ ∷ CX13 ∷ K4⁻ ∷ []) (pw2 c4 (K4⁻ ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ []) (CX13 ∷ CS03⁻ ∷ CX13 ∷ K4⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ []) (lw0 c4 (CCZ234 ∷ []) (CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 7 4 (CX13 ∷ CS03⁻ ∷ CX13 ∷ CS34 ∷ []) (pw2 c4 (CS34 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ []) (CX13 ∷ CS03⁻ ∷ CX13 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 6 4 (CX13 ∷ CS03⁻ ∷ CX13 ∷ CX32 ∷ []) (lw4 c4 (CX32 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ []) (CX13 ∷ CS03⁻ ∷ CX13 ∷ CX32 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CX13 ∷ CS24⁻ ∷ []) (lw0 c4 (CS24⁻ ∷ CX13 ∷ []) (CX13 ∷ CS24⁻ ∷ []) tt tt Eq.refl) ▸ done

  b5 : Chain (CS03 ∷ Sb0-1-4-2 ∷ K4 ∷ CS24 ∷ CX32 ∷ CX13 ∷ CS24⁻ ∷ CS03⁻ ∷ CX13 ∷ CX32 ∷ CS34 ∷ K4⁻ ∷ Sb⁻0-1-4-2 ∷ Toff423 ∷ Bx⁻0-1324 ∷ CS01 ∷ []) (CS03 ∷ Sb0-1-4-2 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ K4 ∷ CCZ234 ∷ K4⁻ ∷ Sb⁻0-1-4-2 ∷ Toff423 ∷ Bx⁻0-1324 ∷ CS01 ∷ [])
  b5 = at 6 2 (CS03⁻ ∷ CS24⁻ ∷ []) (pw1 c4 (CS24⁻ ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CS24⁻ ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CX13 ∷ CS24⁻ ∷ []) (lw0 c4 (CS24⁻ ∷ CX13 ∷ []) (CX13 ∷ CS24⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 4 (CX13 ∷ CS03⁻ ∷ CX13 ∷ CX32 ∷ []) (lw4 c4 (CX32 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ []) (CX13 ∷ CS03⁻ ∷ CX13 ∷ CX32 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CX13 ∷ CS24 ∷ []) (lw0 c4 (CS24 ∷ CX13 ∷ []) (CX13 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS03⁻ ∷ CS24 ∷ []) (pw1 c4 (CS24 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CX13 ∷ CS24 ∷ []) (lw0 c4 (CS24 ∷ CX13 ∷ []) (CX13 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 6 5 (CCZ234 ∷ []) (lw0 c4 (CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (CX13 ∷ CS03⁻ ∷ CX13 ∷ K4 ∷ []) (pw2 c4 (K4 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ []) (CX13 ∷ CS03⁻ ∷ CX13 ∷ K4 ∷ []) tt tt Eq.refl) ▸ done

  b6 : Chain (CS03 ∷ Sb0-1-4-2 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ K4 ∷ CCZ234 ∷ K4⁻ ∷ Sb⁻0-1-4-2 ∷ Toff423 ∷ Bx⁻0-1324 ∷ CS01 ∷ []) (CCZ013 ∷ Sb⁻0-1-23-4 ∷ [])
  b6 = at 5 3 (Toff423 ∷ []) (lw0 c4 (K4 ∷ CCZ234 ∷ K4⁻ ∷ []) (Toff423 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (CS14 ∷ []) (refl) ▸
       at 1 4 (CX13 ∷ CS03⁻ ∷ CX13 ∷ CS14 ∷ []) (pw2 c4 (CS14 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ []) (CX13 ∷ CS03⁻ ∷ CX13 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb0-1-4-2 ∷ []) (refl) ▸
       at 4 5 (Sb⁻0-1-32-4 ∷ []) (refl) ▸
       at 4 2 (CS01 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS10-at2332 c4) ▸
       at 5 1 (Sb⁻0-1-23-4 ∷ []) (sym (lem-SBsymd-at0113203442 c4)) ▸
       at 0 5 (CCZ013 ∷ []) (lw4 c4 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | Kd0: 11 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-Kd0 : Complete 4 → ⟪ (Sb⁻0-1-23-4 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-Kd0 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb⁻0-1-23-4 ∷ K0⁻ ∷ []) (CS14 ∷ K0⁻ ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ [])
  b0 = at 0 1 (Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) (refl) ▸
       at 4 2 (K0⁻ ∷ Bx⁻0-1234 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-Kd0 c4) ▸
       at 3 2 (K0⁻ ∷ Toff423 ∷ []) (lw1 c4 (Toff423 ∷ K0⁻ ∷ []) (K0⁻ ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CS14⁻ ∷ []) (refl) ▸
       at 2 2 (K0⁻ ∷ CS14⁻ ∷ []) (pw2 c4 (CS14⁻ ∷ K0⁻ ∷ []) (K0⁻ ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 1 2 (K0⁻ ∷ Toff423 ∷ []) (lw1 c4 (Toff423 ∷ K0⁻ ∷ []) (K0⁻ ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (CS14 ∷ []) (refl) ▸ done

  b1 : Chain (CS14 ∷ K0⁻ ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) (K0⁻ ∷ Sb⁻0-1-23-4 ∷ [])
  b1 = at 0 2 (K0⁻ ∷ CS14 ∷ []) (pw2 c4 (CS14 ∷ K0⁻ ∷ []) (K0⁻ ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Sb0-1-4-3 ∷ []) (refl) ▸
       at 1 5 (Sb⁻0-1-23-4 ∷ []) (refl) ▸ done


-- auto SBOXd(0;1;23;4) | K0 @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-K0-at2332 : Complete 4 → ⟪ (Sb⁻0-1-32-4 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-K0-at2332 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-32-4 ∷ K0 ∷ []) (K0 ∷ Sb⁻0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·32·4⟩ c4) ▸
       at 2 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 1 2 (K0 ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-K0 c4) ▸
       at 0 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | CCZ013 @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ013-at2332 : Complete 4 → ⟪ (Sb⁻0-1-32-4 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ013-at2332 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-32-4 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sb⁻0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·32·4⟩ c4) ▸
       at 2 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 1 2 (CCZ013 ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ013 c4) ▸
       at 0 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | Kd0 @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-Kd0-at2332 : Complete 4 → ⟪ (Sb⁻0-1-32-4 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-Kd0-at2332 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-32-4 ∷ K0⁻ ∷ []) (K0⁻ ∷ Sb⁻0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·32·4⟩ c4) ▸
       at 2 2 (K0⁻ ∷ Sw23 ∷ []) (sym (c₁ (K • iI) (Swap ↑))) ▸
       at 1 2 (K0⁻ ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-Kd0 c4) ▸
       at 0 2 (K0⁻ ∷ Sw23 ∷ []) (sym (c₁ (K • iI) (Swap ↑))) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | TOFF012: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF012 : Complete 4 → ⟪ (Sb⁻0-1-23-4 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF012 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-23-4 ∷ Toff012 ∷ []) (Toff012 ∷ Sb⁻0-1-23-4 ∷ [])
  b0 = at 1 1 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (lw4 c4 (Toff012 ∷ []) (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻0-1-32-4 ∷ []) (lem-SBsymd-at0113203442 c4) ▸
       at 0 2 (K0 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-K0-at2332 c4) ▸
       at 1 2 (CCZ012 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ013-at2332 c4) ▸
       at 2 2 (K0⁻ ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-Kd0-at2332 c4) ▸
       at 3 1 (Sb⁻0-1-23-4 ∷ []) (sym (lem-SBsymd-at0113203442 c4)) ▸
       at 0 3 (Toff012 ∷ []) (lw4 c4 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (Toff012 ∷ []) tt tt Eq.refl) ▸ done


-- CS20-beta-c @2332: 7 steps
lem-CS20-beta-c-at2332 : Complete 4 → ⟪ (CS03 ∷ Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ CS03 ∷ []) ⟫ʷ
lem-CS20-beta-c-at2332 c4 = run b0
  where
  b0 : Chain (CS03 ∷ Bx0-1324 ∷ []) (Bx0-1324 ∷ CS03 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS02 ∷ Sw23 ∷ []) (lem-nat-2-CS03 c4) ▸
       at 2 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ c4) ▸
       at 1 2 (Bx0-1234 ∷ CS02 ∷ []) (lem-CS20-beta-c c4) ▸
       at 0 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ c4) ▸
       at 1 2 (CS03 ∷ Sw23 ∷ []) (lem-nat-2-CS02 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- CS20-beta-c @243243: 7 steps
lem-CS20-beta-c-at243243 : Complete 4 → ⟪ (CS04 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CS04 ∷ []) ⟫ʷ
lem-CS20-beta-c-at243243 c4 = run b0
  where
  b0 : Chain (CS04 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CS04 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS03 ∷ Sw34 ∷ []) (lem-nat-3-CS04 c4) ▸
       at 2 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ c4) ▸
       at 1 2 (Bx0-1324 ∷ CS03 ∷ []) (lem-CS20-beta-c-at2332 c4) ▸
       at 0 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ c4) ▸
       at 1 2 (CS04 ∷ Sw34 ∷ []) (lem-nat-3-CS03 c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOXd(0;1234) | CS40: 9 steps
lem-auto-BOXd⟨0·1234⟩-∣-CS40 : Complete 4 → ⟪ (Bx⁻0-1234 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ Bx⁻0-1234 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CS40 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx⁻0-1234 ∷ CS04 ∷ []) (CS04 ∷ Bx0-1234 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ []) (lem-BOXd-BOX c4) ▸
       at 1 1 (CS04 ∷ []) (pw1 c4 (CS04 ∷ []) (CS04 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx0-1243 ∷ []) (lem-sym34 c4) ▸
       at 0 1 (Bx0-1423 ∷ []) (lem-sym23-at3443 c4) ▸
       at 0 2 (CS04 ∷ Bx0-1423 ∷ []) (sym (lem-CS20-beta-c-at243243 c4)) ▸
       at 1 1 (Bx0-1243 ∷ []) (lem-sym23-at243243 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym34-at3443 c4) ▸
       at 0 1 (CS04 ∷ []) (pw1 c4 (CS04 ∷ []) (CS04 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CS04 ∷ Bx0-1234 ∷ []) (CS04 ∷ Bx⁻0-1234 ∷ [])
  b1 = at 1 1 (Bx⁻0-1234 ∷ []) (sym (lem-BOXd-BOX c4)) ▸ done


-- auto BOXd(0;1234) | CS04: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-CS04 : Complete 4 → ⟪ (Bx⁻0-1234 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ Bx⁻0-1234 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CS04 c4 = run b0
  where
  b0 : Chain (Bx⁻0-1234 ∷ CS04 ∷ []) (CS04 ∷ Bx⁻0-1234 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ []) (lem-BOXd-BOX c4) ▸
       at 0 1 (Bx0-1243 ∷ []) (lem-sym34 c4) ▸
       at 0 1 (Bx0-1423 ∷ []) (lem-sym23-at3443 c4) ▸
       at 0 2 (CS04 ∷ Bx0-1423 ∷ []) (sym (lem-CS20-beta-c-at243243 c4)) ▸
       at 1 1 (Bx0-1243 ∷ []) (lem-sym23-at243243 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym34-at3443 c4) ▸
       at 1 1 (Bx⁻0-1234 ∷ []) (sym (lem-BOXd-BOX c4)) ▸ done


-- CZ10-beta-c @2332: 7 steps
lem-CZ10-beta-c-at2332 : Complete 4 → ⟪ (CZ03 ∷ Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ CZ03 ∷ []) ⟫ʷ
lem-CZ10-beta-c-at2332 c4 = run b0
  where
  b0 : Chain (CZ03 ∷ Bx0-1324 ∷ []) (Bx0-1324 ∷ CZ03 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CZ02 ∷ Sw23 ∷ []) (lem-nat-2-CZ03 c4) ▸
       at 2 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ c4) ▸
       at 1 2 (Bx0-1234 ∷ CZ02 ∷ []) (lem-CZ10-beta-c c4) ▸
       at 0 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ c4) ▸
       at 1 2 (CZ03 ∷ Sw23 ∷ []) (lem-nat-2-CZ02 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- CZ10-beta-c @243243: 7 steps
lem-CZ10-beta-c-at243243 : Complete 4 → ⟪ (CZ04 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CZ04 ∷ []) ⟫ʷ
lem-CZ10-beta-c-at243243 c4 = run b0
  where
  b0 : Chain (CZ04 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CZ04 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CZ03 ∷ Sw34 ∷ []) (lem-nat-3-CZ04 c4) ▸
       at 2 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ c4) ▸
       at 1 2 (Bx0-1324 ∷ CZ03 ∷ []) (lem-CZ10-beta-c-at2332 c4) ▸
       at 0 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ c4) ▸
       at 1 2 (CZ04 ∷ Sw34 ∷ []) (lem-nat-3-CZ03 c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOXd(0;1234) | CZ04: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-CZ04 : Complete 4 → ⟪ (Bx⁻0-1234 ∷ CZ04 ∷ []) ⟫ʷ ≈ ⟪ (CZ04 ∷ Bx⁻0-1234 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CZ04 c4 = run b0
  where
  b0 : Chain (Bx⁻0-1234 ∷ CZ04 ∷ []) (CZ04 ∷ Bx⁻0-1234 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ []) (lem-BOXd-BOX c4) ▸
       at 0 1 (Bx0-1243 ∷ []) (lem-sym34 c4) ▸
       at 0 1 (Bx0-1423 ∷ []) (lem-sym23-at3443 c4) ▸
       at 0 2 (CZ04 ∷ Bx0-1423 ∷ []) (sym (lem-CZ10-beta-c-at243243 c4)) ▸
       at 1 1 (Bx0-1243 ∷ []) (lem-sym23-at243243 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym34-at3443 c4) ▸
       at 1 1 (Bx⁻0-1234 ∷ []) (sym (lem-BOXd-BOX c4)) ▸ done


-- auto BOXd(0;1234) | CZ40: 9 steps
lem-auto-BOXd⟨0·1234⟩-∣-CZ40 : Complete 4 → ⟪ (Bx⁻0-1234 ∷ CZ04 ∷ []) ⟫ʷ ≈ ⟪ (CZ04 ∷ Bx⁻0-1234 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CZ40 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx⁻0-1234 ∷ CZ04 ∷ []) (CZ04 ∷ Bx0-1234 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ []) (lem-BOXd-BOX c4) ▸
       at 1 1 (CZ04 ∷ []) (pw1 c4 (CZ04 ∷ []) (CZ04 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx0-1243 ∷ []) (lem-sym34 c4) ▸
       at 0 1 (Bx0-1423 ∷ []) (lem-sym23-at3443 c4) ▸
       at 0 2 (CZ04 ∷ Bx0-1423 ∷ []) (sym (lem-CZ10-beta-c-at243243 c4)) ▸
       at 1 1 (Bx0-1243 ∷ []) (lem-sym23-at243243 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym34-at3443 c4) ▸
       at 0 1 (CZ04 ∷ []) (pw1 c4 (CZ04 ∷ []) (CZ04 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CZ04 ∷ Bx0-1234 ∷ []) (CZ04 ∷ Bx⁻0-1234 ∷ [])
  b1 = at 1 1 (Bx⁻0-1234 ∷ []) (sym (lem-BOXd-BOX c4)) ▸ done


-- CX10-beta-c @1221: 7 steps
lem-CX10-beta-c-at1221 : Complete 4 → ⟪ (CX20 ∷ Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ CX20 ∷ []) ⟫ʷ
lem-CX10-beta-c-at1221 c4 = run b0
  where
  b0 : Chain (CX20 ∷ Bx0-2134 ∷ []) (Bx0-2134 ∷ CX20 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CX10 ∷ Sw12 ∷ []) (lem-nat-1-CX20 c4) ▸
       at 2 2 (Bx0-1234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2134⟩ c4) ▸
       at 1 2 (Bx0-1234 ∷ CX10 ∷ []) (lem-CX10-beta-c c4) ▸
       at 0 2 (Bx0-2134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1234⟩ c4) ▸
       at 1 2 (CX20 ∷ Sw12 ∷ []) (lem-nat-1-CX10 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- CX10-beta-c @132132: 7 steps
lem-CX10-beta-c-at132132 : Complete 4 → ⟪ (CX30 ∷ Bx0-3124 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ CX30 ∷ []) ⟫ʷ
lem-CX10-beta-c-at132132 c4 = run b0
  where
  b0 : Chain (CX30 ∷ Bx0-3124 ∷ []) (Bx0-3124 ∷ CX30 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CX20 ∷ Sw23 ∷ []) (lem-nat-2-CX30 c4) ▸
       at 2 2 (Bx0-2134 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3124⟩ c4) ▸
       at 1 2 (Bx0-2134 ∷ CX20 ∷ []) (lem-CX10-beta-c-at1221 c4) ▸
       at 0 2 (Bx0-3124 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2134⟩ c4) ▸
       at 1 2 (CX30 ∷ Sw23 ∷ []) (lem-nat-2-CX20 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- CX10-beta-c @14213243: 7 steps
lem-CX10-beta-c-at14213243 : Complete 4 → ⟪ (CX40 ∷ Bx0-4123 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4123 ∷ CX40 ∷ []) ⟫ʷ
lem-CX10-beta-c-at14213243 c4 = run b0
  where
  b0 : Chain (CX40 ∷ Bx0-4123 ∷ []) (Bx0-4123 ∷ CX40 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CX30 ∷ Sw34 ∷ []) (lem-nat-3-CX40 c4) ▸
       at 2 2 (Bx0-3124 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·4123⟩ c4) ▸
       at 1 2 (Bx0-3124 ∷ CX30 ∷ []) (lem-CX10-beta-c-at132132 c4) ▸
       at 0 2 (Bx0-4123 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·3124⟩ c4) ▸
       at 1 2 (CX40 ∷ Sw34 ∷ []) (lem-nat-3-CX30 c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOXd(0;1234) | CX40: 9 steps
lem-auto-BOXd⟨0·1234⟩-∣-CX40 : Complete 4 → ⟪ (Bx⁻0-1234 ∷ CX40 ∷ []) ⟫ʷ ≈ ⟪ (CX40 ∷ Bx⁻0-1234 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CX40 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx⁻0-1234 ∷ CX40 ∷ []) (CX40 ∷ Bx0-1234 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ []) (lem-BOXd-BOX c4) ▸
       at 0 1 (Bx0-1243 ∷ []) (lem-sym34 c4) ▸
       at 0 1 (Bx0-1423 ∷ []) (lem-sym23-at3443 c4) ▸
       at 0 1 (Bx0-4123 ∷ []) (lem-sym12-at243243 c4) ▸
       at 0 2 (CX40 ∷ Bx0-4123 ∷ []) (sym (lem-CX10-beta-c-at14213243 c4)) ▸
       at 1 1 (Bx0-1423 ∷ []) (lem-sym12-at14213243 c4) ▸
       at 1 1 (Bx0-1243 ∷ []) (lem-sym23-at243243 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym34-at3443 c4) ▸ done

  b1 : Chain (CX40 ∷ Bx0-1234 ∷ []) (CX40 ∷ Bx⁻0-1234 ∷ [])
  b1 = at 1 1 (Bx⁻0-1234 ∷ []) (sym (lem-BOXd-BOX c4)) ▸ done


-- CS20-beta-ci @2332: 7 steps
lem-CS20-beta-ci-at2332 : Complete 4 → ⟪ (CS03⁻ ∷ Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-CS20-beta-ci-at2332 c4 = run b0
  where
  b0 : Chain (CS03⁻ ∷ Bx0-1324 ∷ []) (Bx0-1324 ∷ CS03⁻ ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS02⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd03 c4) ▸
       at 2 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ c4) ▸
       at 1 2 (Bx0-1234 ∷ CS02⁻ ∷ []) (lem-CS20-beta-ci c4) ▸
       at 0 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ c4) ▸
       at 1 2 (CS03⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd02 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- CS20-beta-ci @243243: 7 steps
lem-CS20-beta-ci-at243243 : Complete 4 → ⟪ (CS04⁻ ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CS04⁻ ∷ []) ⟫ʷ
lem-CS20-beta-ci-at243243 c4 = run b0
  where
  b0 : Chain (CS04⁻ ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CS04⁻ ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS03⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd04 c4) ▸
       at 2 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ c4) ▸
       at 1 2 (Bx0-1324 ∷ CS03⁻ ∷ []) (lem-CS20-beta-ci-at2332 c4) ▸
       at 0 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ c4) ▸
       at 1 2 (CS04⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd03 c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOXd(0;1234) | CSd40: 9 steps
lem-auto-BOXd⟨0·1234⟩-∣-CSd40 : Complete 4 → ⟪ (Bx⁻0-1234 ∷ CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS04⁻ ∷ Bx⁻0-1234 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CSd40 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx⁻0-1234 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ Bx0-1234 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ []) (lem-BOXd-BOX c4) ▸
       at 1 1 (CS04⁻ ∷ []) (pw1 c4 (CS04⁻ ∷ []) (CS04⁻ ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx0-1243 ∷ []) (lem-sym34 c4) ▸
       at 0 1 (Bx0-1423 ∷ []) (lem-sym23-at3443 c4) ▸
       at 0 2 (CS04⁻ ∷ Bx0-1423 ∷ []) (sym (lem-CS20-beta-ci-at243243 c4)) ▸
       at 1 1 (Bx0-1243 ∷ []) (lem-sym23-at243243 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym34-at3443 c4) ▸
       at 0 1 (CS04⁻ ∷ []) (pw1 c4 (CS04⁻ ∷ []) (CS04⁻ ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CS04⁻ ∷ Bx0-1234 ∷ []) (CS04⁻ ∷ Bx⁻0-1234 ∷ [])
  b1 = at 1 1 (Bx⁻0-1234 ∷ []) (sym (lem-BOXd-BOX c4)) ▸ done


-- auto CCZ012 | BOX(3;0142): 1 steps
lem-auto-CCZ012-∣-BOX⟨3·0142⟩ : Complete 4 → ⟪ (CCZ012 ∷ Bx3-0142 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0142 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·0142⟩ c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Bx3-0142 ∷ []) (Bx3-0142 ∷ CCZ012 ∷ [])
  b0 = at 0 2 (Bx3-0142 ∷ CCZ012 ∷ []) (lem-c124-beta-at0310213442 c4) ▸ done


-- auto SBOX(0;1;23;4) | K0: 11 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-K0 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-K0 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-23-4 ∷ K0 ∷ []) (Bx0-1234 ∷ Toff423 ∷ K0 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 1 (CS14⁻ ∷ []) (refl) ▸
       at 4 2 (K0 ∷ CS14⁻ ∷ []) (pw2 c4 (CS14⁻ ∷ K0 ∷ []) (K0 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 3 2 (K0 ∷ Toff423 ∷ []) (lw1 c4 (Toff423 ∷ K0 ∷ []) (K0 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CS14 ∷ []) (refl) ▸
       at 2 2 (K0 ∷ CS14 ∷ []) (pw2 c4 (CS14 ∷ K0 ∷ []) (K0 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb0-1-4-3 ∷ []) (refl) ▸ done

  b1 : Chain (Bx0-1234 ∷ Toff423 ∷ K0 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (K0 ∷ Sb0-1-23-4 ∷ [])
  b1 = at 1 2 (K0 ∷ Toff423 ∷ []) (lw1 c4 (Toff423 ∷ K0 ∷ []) (K0 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (K0 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-K0 c4) ▸
       at 1 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- auto BOX(0;1234) | CS30: 5 steps
lem-auto-BOX⟨0·1234⟩-∣-CS30 : Complete 4 → ⟪ (Bx0-1234 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS30 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CS03 ∷ []) (CS03 ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (CS03 ∷ []) (lw4 c4 (CS03 ∷ []) (CS03 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 0 2 (CS03 ∷ Bx0-1324 ∷ []) (sym (lem-CS20-beta-c-at2332 c4)) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸
       at 0 1 (CS03 ∷ []) (lw4 c4 (CS03 ∷ []) (CS03 ∷ []) tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CS30: 11 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS30 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS30 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-23-4 ∷ CS03 ∷ []) (Bx0-1234 ∷ Toff423 ∷ CS03 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 1 (CS14⁻ ∷ []) (refl) ▸
       at 4 2 (CS03 ∷ CS14⁻ ∷ []) (pw2 c4 (CS14⁻ ∷ CS03 ∷ []) (CS03 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 3 2 (CS03 ∷ Toff423 ∷ []) (pw1 c4 (Toff423 ∷ CS03 ∷ []) (CS03 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CS14 ∷ []) (refl) ▸
       at 2 2 (CS03 ∷ CS14 ∷ []) (pw2 c4 (CS14 ∷ CS03 ∷ []) (CS03 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb0-1-4-3 ∷ []) (refl) ▸ done

  b1 : Chain (Bx0-1234 ∷ Toff423 ∷ CS03 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (CS03 ∷ Sb0-1-23-4 ∷ [])
  b1 = at 1 2 (CS03 ∷ Toff423 ∷ []) (pw1 c4 (Toff423 ∷ CS03 ∷ []) (CS03 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (CS03 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS30 c4) ▸
       at 1 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- auto BOX(0;1234) | CCZ214: 3 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ214 : Complete 4 → ⟪ (Bx0-1234 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ214 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ []) (lw0 c4 (CCZ124 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (CCZ124 ∷ Bx0-1234 ∷ []) (sym (lem-c124-beta c4)) ▸
       at 0 1 (CCZ124 ∷ []) (lw0 c4 (CCZ124 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CSd30: 5 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd30 : Complete 4 → ⟪ (Bx0-1234 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd30 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (CS03⁻ ∷ []) (lw4 c4 (CS03⁻ ∷ []) (CS03⁻ ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 0 2 (CS03⁻ ∷ Bx0-1324 ∷ []) (sym (lem-CS20-beta-ci-at2332 c4)) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸
       at 0 1 (CS03⁻ ∷ []) (lw4 c4 (CS03⁻ ∷ []) (CS03⁻ ∷ []) tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CS10: 5 steps
lem-auto-BOX⟨0·1234⟩-∣-CS10 : Complete 4 → ⟪ (Bx0-1234 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS10 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CS01 ∷ []) (CS01 ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (CS01 ∷ []) (lw4 c4 (CS01 ∷ []) (CS01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 0 2 (CS01 ∷ Bx0-2134 ∷ []) (sym (lem-CS20-beta-c-at1221 c4)) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸
       at 0 1 (CS01 ∷ []) (lw4 c4 (CS01 ∷ []) (CS01 ∷ []) tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CS10: 11 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS10 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS10 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-23-4 ∷ CS01 ∷ []) (Bx0-1234 ∷ Toff423 ∷ CS01 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 1 (CS14⁻ ∷ []) (refl) ▸
       at 4 2 (CS01 ∷ CS14⁻ ∷ []) (pw2 c4 (CS14⁻ ∷ CS01 ∷ []) (CS01 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 3 2 (CS01 ∷ Toff423 ∷ []) (lem-auto-TOFF012-∣-CS34-at0412233140 c4) ▸
       at 2 1 (CS14 ∷ []) (refl) ▸
       at 2 2 (CS01 ∷ CS14 ∷ []) (pw2 c4 (CS14 ∷ CS01 ∷ []) (CS01 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb0-1-4-3 ∷ []) (refl) ▸ done

  b1 : Chain (Bx0-1234 ∷ Toff423 ∷ CS01 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (CS01 ∷ Sb0-1-23-4 ∷ [])
  b1 = at 1 2 (CS01 ∷ Toff423 ∷ []) (lem-auto-TOFF012-∣-CS34-at0412233140 c4) ▸
       at 0 2 (CS01 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS10 c4) ▸
       at 1 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- auto SBOX(0;1;23;4) | CS30 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS30-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS30-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CS02 ∷ []) (CS02 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (CS03 ∷ Sw23 ∷ []) (lem-nat-2-CS02 c4) ▸
       at 1 2 (CS03 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS30 c4) ▸
       at 0 2 (CS02 ∷ Sw23 ∷ []) (lem-nat-2-CS03 c4) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- CX23-beta @1221: 8 steps
lem-CX23-beta-at1221 : Complete 4 → ⟪ (CX13 ∷ Bx0-2134 ∷ CX13 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CX23-beta-at1221 c4 = run b0
  where
  b0 : Chain (CX13 ∷ Bx0-2134 ∷ CX13 ∷ []) (Bx0-2134 ∷ CCZ124 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CX23 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CX13 ∷ []) (CX23 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-1234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2134⟩ c4) ▸
       at 3 2 (CX23 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CX13 ∷ []) (CX23 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Bx0-1234 ∷ CCZ124 ∷ []) (lem-CX23-beta c4) ▸
       at 0 2 (Bx0-2134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1234⟩ c4) ▸
       at 1 2 (CCZ124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- CX23-beta @132132: 8 steps
lem-CX23-beta-at132132 : Complete 4 → ⟪ (CX12 ∷ Bx0-3124 ∷ CX12 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CX23-beta-at132132 c4 = run b0
  where
  b0 : Chain (CX12 ∷ Bx0-3124 ∷ CX12 ∷ []) (Bx0-3124 ∷ CCZ134 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CX13 ∷ Sw23 ∷ []) (lem-nat-2-CX12 c4) ▸
       at 2 2 (Bx0-2134 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3124⟩ c4) ▸
       at 3 2 (CX13 ∷ Sw23 ∷ []) (lem-nat-2-CX12 c4) ▸
       at 1 3 (Bx0-2134 ∷ CCZ124 ∷ []) (lem-CX23-beta-at1221 c4) ▸
       at 0 2 (Bx0-3124 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2134⟩ c4) ▸
       at 1 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ214 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ214-at2332 : Complete 4 → ⟪ (Bx0-1324 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ214-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ CCZ134 ∷ []) (CCZ134 ∷ Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ c4) ▸
       at 2 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 1 2 (CCZ124 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ214 c4) ▸
       at 0 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 1 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CSd30 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd30-at2332 : Complete 4 → ⟪ (Bx0-1324 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd30-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ c4) ▸
       at 2 2 (CS03⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd02 c4) ▸
       at 1 2 (CS03⁻ ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd30 c4) ▸
       at 0 2 (CS02⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd03 c4) ▸
       at 1 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CS10 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS10-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS10-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CS01 ∷ []) (CS01 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (CS01 ∷ Sw23 ∷ []) (sym (c₂ (CS) (Swap))) ▸
       at 1 2 (CS01 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS10 c4) ▸
       at 0 2 (CS01 ∷ Sw23 ∷ []) (sym (c₂ (CS) (Swap))) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CCZ012: 60 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ012 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ012 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (Sb0-1-23-4 ∷ CCZ012 ∷ []) (CS02 ∷ Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ K4 ∷ CCZ234 ∷ K4⁻ ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ Sb⁻0-1-4-2 ∷ CS01 ∷ [])
  b0 = at 1 1 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS02 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS30-at2332 c4) ▸
       at 1 1 (Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ []) (refl) ▸
       at 5 1 (CS14⁻ ∷ []) (refl) ▸
       at 5 4 (CX12 ∷ CS02⁻ ∷ CX12 ∷ CS14⁻ ∷ []) (pw3 c4 (CS14⁻ ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ []) (CX12 ∷ CS02⁻ ∷ CX12 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 8 1 (Sb⁻0-1-4-2 ∷ []) (refl) ▸
       at 4 1 (K4 ∷ CCZ234 ∷ K4⁻ ∷ []) (lw0 c4 (Toff423 ∷ []) (K4 ∷ CCZ234 ∷ K4⁻ ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CS02 ∷ Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ K4 ∷ CCZ234 ∷ K4⁻ ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ Sb⁻0-1-4-2 ∷ CS01 ∷ []) (CS02 ∷ Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ K4 ∷ CS34 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K4⁻ ∷ Sb⁻0-1-4-2 ∷ CS01 ∷ [])
  b1 = at 6 4 (CX12 ∷ CS02⁻ ∷ CX12 ∷ K4⁻ ∷ []) (lw3 c4 (K4⁻ ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ []) (CX12 ∷ CS02⁻ ∷ CX12 ∷ K4⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) (lw0 c4 (CCZ234 ∷ []) (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 9 4 (CX12 ∷ CS02⁻ ∷ CX12 ∷ CS24 ∷ []) (pw3 c4 (CS24 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ []) (CX12 ∷ CS02⁻ ∷ CX12 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 8 4 (CX12 ∷ CS02⁻ ∷ CX12 ∷ CX23 ∷ []) (lw4 c4 (CX23 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ []) (CX12 ∷ CS02⁻ ∷ CX12 ∷ CX23 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CX12 ∷ CS34⁻ ∷ []) (sym (c₃ (CX₀₁ ↑) (CS • CS • CS))) ▸
       at 8 2 (CS02⁻ ∷ CS34⁻ ∷ []) (sym (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (CS • CS • CS))) ▸
       at 9 2 (CX12 ∷ CS34⁻ ∷ []) (sym (c₃ (CX₀₁ ↑) (CS • CS • CS))) ▸
       at 6 4 (CX12 ∷ CS02⁻ ∷ CX12 ∷ CX23 ∷ []) (lw4 c4 (CX23 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ []) (CX12 ∷ CS02⁻ ∷ CX12 ∷ CX23 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (CS02 ∷ Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ K4 ∷ CS34 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K4⁻ ∷ Sb⁻0-1-4-2 ∷ CS01 ∷ []) (CS02 ∷ Bx0-1324 ∷ Toff423 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS14 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS01 ∷ [])
  b2 = at 5 2 (CX12 ∷ CS34 ∷ []) (sym (c₃ (CX₀₁ ↑) (CS))) ▸
       at 6 2 (CS02⁻ ∷ CS34 ∷ []) (sym (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (CS))) ▸
       at 7 2 (CX12 ∷ CS34 ∷ []) (sym (c₃ (CX₀₁ ↑) (CS))) ▸
       at 8 5 (CCZ234 ∷ []) (lw0 c4 (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 4 4 (CX12 ∷ CS02⁻ ∷ CX12 ∷ K4 ∷ []) (lw3 c4 (K4 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ []) (CX12 ∷ CS02⁻ ∷ CX12 ∷ K4 ∷ []) tt tt Eq.refl) ▸
       at 7 3 (Toff423 ∷ []) (lw0 c4 (K4 ∷ CCZ234 ∷ K4⁻ ∷ []) (Toff423 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CS14 ∷ []) (refl) ▸
       at 3 4 (CX12 ∷ CS02⁻ ∷ CX12 ∷ CS14 ∷ []) (pw3 c4 (CS14 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ []) (CX12 ∷ CS02⁻ ∷ CX12 ∷ CS14 ∷ []) tt tt Eq.refl) ▸ done

  b3 : Chain (CS02 ∷ Bx0-1324 ∷ Toff423 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS14 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS01 ∷ []) (CS02 ∷ Bx0-1324 ∷ K4 ∷ CS34 ∷ CX23 ∷ CX12 ∷ CS02⁻ ∷ CS34⁻ ∷ CX12 ∷ CX23 ∷ CS24 ∷ K4⁻ ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS01 ∷ [])
  b3 = at 6 1 (Sb0-1-4-2 ∷ []) (refl) ▸
       at 2 1 (K4 ∷ CCZ234 ∷ K4⁻ ∷ []) (lw0 c4 (Toff423 ∷ []) (K4 ∷ CCZ234 ∷ K4⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 4 (CX12 ∷ CS02⁻ ∷ CX12 ∷ K4⁻ ∷ []) (lw3 c4 (K4⁻ ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ []) (CX12 ∷ CS02⁻ ∷ CX12 ∷ K4⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) (lw0 c4 (CCZ234 ∷ []) (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 7 4 (CX12 ∷ CS02⁻ ∷ CX12 ∷ CS24 ∷ []) (pw3 c4 (CS24 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ []) (CX12 ∷ CS02⁻ ∷ CX12 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 6 4 (CX12 ∷ CS02⁻ ∷ CX12 ∷ CX23 ∷ []) (lw4 c4 (CX23 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ []) (CX12 ∷ CS02⁻ ∷ CX12 ∷ CX23 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CX12 ∷ CS34⁻ ∷ []) (sym (c₃ (CX₀₁ ↑) (CS • CS • CS))) ▸
       at 6 2 (CS02⁻ ∷ CS34⁻ ∷ []) (sym (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (CS • CS • CS))) ▸ done

  b4 : Chain (CS02 ∷ Bx0-1324 ∷ K4 ∷ CS34 ∷ CX23 ∷ CX12 ∷ CS02⁻ ∷ CS34⁻ ∷ CX12 ∷ CX23 ∷ CS24 ∷ K4⁻ ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS01 ∷ []) (CS02 ∷ Bx0-1324 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS01 ∷ [])
  b4 = at 7 2 (CX12 ∷ CS34⁻ ∷ []) (sym (c₃ (CX₀₁ ↑) (CS • CS • CS))) ▸
       at 4 4 (CX12 ∷ CS02⁻ ∷ CX12 ∷ CX23 ∷ []) (lw4 c4 (CX23 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ []) (CX12 ∷ CS02⁻ ∷ CX12 ∷ CX23 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CX12 ∷ CS34 ∷ []) (sym (c₃ (CX₀₁ ↑) (CS))) ▸
       at 4 2 (CS02⁻ ∷ CS34 ∷ []) (sym (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (CS))) ▸
       at 5 2 (CX12 ∷ CS34 ∷ []) (sym (c₃ (CX₀₁ ↑) (CS))) ▸
       at 6 5 (CCZ234 ∷ []) (lw0 c4 (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (CX12 ∷ CS02⁻ ∷ CX12 ∷ K4 ∷ []) (lw3 c4 (K4 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ []) (CX12 ∷ CS02⁻ ∷ CX12 ∷ K4 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (Toff423 ∷ []) (lw0 c4 (K4 ∷ CCZ234 ∷ K4⁻ ∷ []) (Toff423 ∷ []) tt tt Eq.refl) ▸ done

  b5 : Chain (CS02 ∷ Bx0-1324 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS01 ∷ []) (CS02 ∷ CX12 ∷ CCZ134 ∷ CS02⁻ ∷ CX12 ∷ CX12 ∷ Bx0-3124 ∷ CX12 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS01 ∷ [])
  b5 = at 1 0 (CX12 ∷ CX12 ∷ []) (lw4 c4 [] (CX12 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Bx0-3124 ∷ []) (lem-sym12-at2332 c4) ▸
       at 2 3 (Bx0-3124 ∷ CCZ134 ∷ []) (lem-CX23-beta-at132132 c4) ▸
       at 2 1 (Bx0-1324 ∷ []) (lem-sym12-at132132 c4) ▸
       at 2 2 (CCZ134 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ214-at2332 c4) ▸
       at 3 2 (CS02⁻ ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd30-at2332 c4) ▸
       at 4 0 (CX12 ∷ CX12 ∷ []) (lw4 c4 [] (CX12 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Bx0-3124 ∷ []) (lem-sym12-at2332 c4) ▸ done

  b6 : Chain (CS02 ∷ CX12 ∷ CCZ134 ∷ CS02⁻ ∷ CX12 ∷ CX12 ∷ Bx0-3124 ∷ CX12 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS01 ∷ []) (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS01 ∷ [])
  b6 = at 5 3 (Bx0-3124 ∷ CCZ134 ∷ []) (lem-CX23-beta-at132132 c4) ▸
       at 5 1 (Bx0-1324 ∷ []) (lem-sym12-at132132 c4) ▸
       at 5 2 (CCZ134 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ214-at2332 c4) ▸
       at 1 2 (CCZ134 ∷ CX12 ∷ []) (lw0 c4 (CX12 ∷ CCZ134 ∷ []) (CCZ134 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ134 ∷ CX12 ∷ []) (lw0 c4 (CX12 ∷ CCZ134 ∷ []) (CCZ134 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ134 ∷ CS02⁻ ∷ []) (lem-comm-CSd02-CCZ134 c4) ▸
       at 2 2 (CCZ134 ∷ CX12 ∷ []) (lw0 c4 (CX12 ∷ CCZ134 ∷ []) (CCZ134 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 [] (lw0 c4 (CCZ134 ∷ CCZ134 ∷ []) [] tt tt Eq.refl) ▸ done

  b7 : Chain (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS01 ∷ []) (CCZ012 ∷ Sb0-1-23-4 ∷ [])
  b7 = at 4 5 (Sb0-1-32-4 ∷ []) (refl) ▸
       at 4 2 (CS01 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS10-at2332 c4) ▸
       at 5 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 5 (CCZ012 ∷ []) (lw4 c4 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | Kd0: 11 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd0 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd0 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-23-4 ∷ K0⁻ ∷ []) (Bx0-1234 ∷ Toff423 ∷ K0⁻ ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 1 (CS14⁻ ∷ []) (refl) ▸
       at 4 2 (K0⁻ ∷ CS14⁻ ∷ []) (pw2 c4 (CS14⁻ ∷ K0⁻ ∷ []) (K0⁻ ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 3 2 (K0⁻ ∷ Toff423 ∷ []) (lw1 c4 (Toff423 ∷ K0⁻ ∷ []) (K0⁻ ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CS14 ∷ []) (refl) ▸
       at 2 2 (K0⁻ ∷ CS14 ∷ []) (pw2 c4 (CS14 ∷ K0⁻ ∷ []) (K0⁻ ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb0-1-4-3 ∷ []) (refl) ▸ done

  b1 : Chain (Bx0-1234 ∷ Toff423 ∷ K0⁻ ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (K0⁻ ∷ Sb0-1-23-4 ∷ [])
  b1 = at 1 2 (K0⁻ ∷ Toff423 ∷ []) (lw1 c4 (Toff423 ∷ K0⁻ ∷ []) (K0⁻ ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (K0⁻ ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-Kd0 c4) ▸
       at 1 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- auto SBOX(0;1;23;4) | K0 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ K0 ∷ []) (K0 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 1 2 (K0 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K0 c4) ▸
       at 0 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CCZ012 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ012-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ012-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 1 2 (CCZ012 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ012 c4) ▸
       at 0 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | Kd0 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd0-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd0-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ K0⁻ ∷ []) (K0⁻ ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (K0⁻ ∷ Sw23 ∷ []) (sym (c₁ (K • iI) (Swap ↑))) ▸
       at 1 2 (K0⁻ ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd0 c4) ▸
       at 0 2 (K0⁻ ∷ Sw23 ∷ []) (sym (c₁ (K • iI) (Swap ↑))) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | TOFF013: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF013 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF013 c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ Toff013 ∷ []) (Toff013 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 1 1 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (lw4 c4 (Toff013 ∷ []) (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (K0 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at2332 c4) ▸
       at 1 2 (CCZ013 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ012-at2332 c4) ▸
       at 2 2 (K0⁻ ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd0-at2332 c4) ▸
       at 3 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 3 (Toff013 ∷ []) (lw4 c4 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (Toff013 ∷ []) tt tt Eq.refl) ▸ done


-- CS12-beta @13243142: 7 steps
lem-CS12-beta-at13243142 : Complete 4 → ⟪ (CS34 ∷ Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ CS34 ∷ []) ⟫ʷ
lem-CS12-beta-at13243142 c4 = run b0
  where
  b0 : Chain (CS34 ∷ Bx0-3412 ∷ []) (Bx0-3412 ∷ CS34 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS24 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS34 ∷ []) (CS24 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-2413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3412⟩ c4) ▸
       at 1 2 (Bx0-2413 ∷ CS24 ∷ []) (lem-CS12-beta-at12243143 c4) ▸
       at 0 2 (Bx0-3412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2413⟩ c4) ▸
       at 1 2 (CS34 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS24 ∷ []) (CS34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CS43: 11 steps
lem-auto-BOX⟨0·1234⟩-∣-CS43 : Complete 4 → ⟪ (Bx0-1234 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS43 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-1234 ∷ CS34 ∷ []) (CS34 ∷ Bx0-3124 ∷ [])
  b0 = at 1 1 (CS34 ∷ []) (lw0 c4 (CS34 ∷ []) (CS34 ∷ []) tt tt Eq.refl) ▸
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
       at 0 1 (CS34 ∷ []) (lw0 c4 (CS34 ∷ []) (CS34 ∷ []) tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CS43: 9 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS43 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS43 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-23-4 ∷ CS34 ∷ []) (CS34 ∷ Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 1 (CS14⁻ ∷ []) (refl) ▸
       at 4 2 (CS34 ∷ CS14⁻ ∷ []) (lw0 c4 (CS14⁻ ∷ CS34 ∷ []) (CS34 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 2 1 (CS14 ∷ []) (refl) ▸
       at 1 4 (CS34 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ []) (lw0 c4 (Toff423 ∷ CS14 ∷ Toff423 ∷ CS34 ∷ []) (CS34 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb0-1-4-3 ∷ []) (refl) ▸
       at 0 2 (CS34 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS43 c4) ▸ done

  b1 : Chain (CS34 ∷ Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (CS34 ∷ Sb0-1-23-4 ∷ [])
  b1 = at 1 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- auto BOX(0;1234) | CS03: 3 steps
lem-auto-BOX⟨0·1234⟩-∣-CS03 : Complete 4 → ⟪ (Bx0-1234 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS03 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CS03 ∷ []) (CS03 ∷ Bx0-1234 ∷ [])
  b0 = at 0 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 0 2 (CS03 ∷ Bx0-1324 ∷ []) (sym (lem-CS20-beta-c-at2332 c4)) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸ done


-- auto SBOX(0;1;23;4) | CS03: 11 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS03 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS03 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-23-4 ∷ CS03 ∷ []) (Bx0-1234 ∷ Toff423 ∷ CS03 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 1 (CS14⁻ ∷ []) (refl) ▸
       at 4 2 (CS03 ∷ CS14⁻ ∷ []) (pw2 c4 (CS14⁻ ∷ CS03 ∷ []) (CS03 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 3 2 (CS03 ∷ Toff423 ∷ []) (pw1 c4 (Toff423 ∷ CS03 ∷ []) (CS03 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CS14 ∷ []) (refl) ▸
       at 2 2 (CS03 ∷ CS14 ∷ []) (pw2 c4 (CS14 ∷ CS03 ∷ []) (CS03 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb0-1-4-3 ∷ []) (refl) ▸ done

  b1 : Chain (Bx0-1234 ∷ Toff423 ∷ CS03 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (CS03 ∷ Sb0-1-23-4 ∷ [])
  b1 = at 1 2 (CS03 ∷ Toff423 ∷ []) (pw1 c4 (Toff423 ∷ CS03 ∷ []) (CS03 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (CS03 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS03 c4) ▸
       at 1 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- auto BOX(0;1234) | CS34: 9 steps
lem-auto-BOX⟨0·1234⟩-∣-CS34 : Complete 4 → ⟪ (Bx0-1234 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ Bx0-1234 ∷ []) ⟫ʷ
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
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS34 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS34 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-23-4 ∷ CS34 ∷ []) (CS34 ∷ Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 1 (CS14⁻ ∷ []) (refl) ▸
       at 4 2 (CS34 ∷ CS14⁻ ∷ []) (lw0 c4 (CS14⁻ ∷ CS34 ∷ []) (CS34 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 2 1 (CS14 ∷ []) (refl) ▸
       at 1 4 (CS34 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ []) (lw0 c4 (Toff423 ∷ CS14 ∷ Toff423 ∷ CS34 ∷ []) (CS34 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb0-1-4-3 ∷ []) (refl) ▸
       at 0 2 (CS34 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS34 c4) ▸ done

  b1 : Chain (CS34 ∷ Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (CS34 ∷ Sb0-1-23-4 ∷ [])
  b1 = at 1 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- auto BOX(0;1234) | CS20: 3 steps
lem-auto-BOX⟨0·1234⟩-∣-CS20 : Complete 4 → ⟪ (Bx0-1234 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS20 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CS02 ∷ []) (CS02 ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (CS02 ∷ []) (lw4 c4 (CS02 ∷ []) (CS02 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (CS02 ∷ Bx0-1234 ∷ []) (sym (lem-CS20-beta-c c4)) ▸
       at 0 1 (CS02 ∷ []) (lw4 c4 (CS02 ∷ []) (CS02 ∷ []) tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CS20: 11 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS20 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS20 c4 = trans (run b0) (run b1)
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
       at 0 2 (CS02 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS20 c4) ▸
       at 1 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- auto BOX(0;1234) | CCZ314: 5 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ314 : Complete 4 → ⟪ (Bx0-1234 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ314 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CCZ134 ∷ []) (CCZ134 ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ []) (lw0 c4 (CCZ134 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 0 2 (CCZ134 ∷ Bx0-1324 ∷ []) (sym (lem-c124-beta-at2332 c4)) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸
       at 0 1 (CCZ134 ∷ []) (lw0 c4 (CCZ134 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CSd20: 3 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd20 : Complete 4 → ⟪ (Bx0-1234 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd20 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (CS02⁻ ∷ []) (lw4 c4 (CS02⁻ ∷ []) (CS02⁻ ∷ []) tt tt Eq.refl) ▸
       at 0 2 (CS02⁻ ∷ Bx0-1234 ∷ []) (sym (lem-CS20-beta-ci c4)) ▸
       at 0 1 (CS02⁻ ∷ []) (lw4 c4 (CS02⁻ ∷ []) (CS02⁻ ∷ []) tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CS20 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS20-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS20-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CS03 ∷ []) (CS03 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (CS02 ∷ Sw23 ∷ []) (lem-nat-2-CS03 c4) ▸
       at 1 2 (CS02 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS20 c4) ▸
       at 0 2 (CS03 ∷ Sw23 ∷ []) (lem-nat-2-CS02 c4) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ314 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ314-at2332 : Complete 4 → ⟪ (Bx0-1324 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ314-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ c4) ▸
       at 2 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 1 2 (CCZ134 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ314 c4) ▸
       at 0 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 1 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


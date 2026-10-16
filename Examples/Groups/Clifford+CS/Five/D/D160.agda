{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D160 where

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
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-CS20-beta-ci ; lem-auto-CCZ012-∣-CCZ314 ; lem-sym12 ; lem-sym23 ; lem-sym34)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-beta-T-at14213243 ; lem-sym12-at1221 ; lem-sym23-at1221)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-c124-beta-at2332 ; lem-sym23-at122331 ; lem-sym23-at2332 ; lem-sym23-at243243 ; lem-sym23-at3443 ; lem-sym34-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS23-at2332 ; lem-beta-T-at0310243142)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-F5-CS01 ; lem-auto-BOX⟨0·1234⟩-∣-CS13)
open import Examples.Groups.Clifford+CS.Five.D.D007 using (lem-SBsym-at0113203442 ; lem-auto-BOX⟨0·1234⟩-∣-K0 ; lem-auto-BOX⟨0·1234⟩-∣-Kd0)
open import Examples.Groups.Clifford+CS.Five.D.D009 using (lem-CS20-beta-c-at243243 ; lem-CS20-beta-ci-at243243 ; lem-CX23-beta-at1221 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ314-at2332 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CS03 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CS10-at2332 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at2332 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd0-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D010 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS14-at2332 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd14-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D079 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS43-at2332 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd43-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D080 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-CX20)
open import Examples.Groups.Clifford+CS.Five.D.D135 using (lem-CSd12-beta-at122331 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CS02-at2332 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CS12-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D136 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ314 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CX14-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D138 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd03-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D145 using (lem-sym23-at143143)
open import Examples.Groups.Clifford+CS.Five.D.D159 using (lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at3443)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-CCZ023 ; lem-nat-1-TOFF014 ; lem-nat-2-BOX⟨0·1234⟩ ; lem-nat-2-BOX⟨0·1324⟩ ; lem-nat-3-BOX⟨0·1423⟩)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-1-CCZ013 ; lem-nat-3-BOX⟨0·1324⟩)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-2-CCZ124 ; lem-nat-2-CCZ134)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-0-TOFF304)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-0-BOX⟨0·4123⟩ ; lem-nat-1-TOFF304)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-0-BOX⟨0·1423⟩ ; lem-nat-0-TOFF024 ; lem-nat-1-BOX⟨1·0423⟩)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-0-BOX⟨1·0423⟩ ; lem-nat-1-BOX⟨2·0413⟩ ; lem-nat-3-CCZ123 ; lem-nat-3-CCZ124)
open import Examples.Groups.Clifford+CS.Five.D.R013 using (lem-nat-2-CS12 ; lem-nat-2-CS13)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-0-SBOX⟨0·1·42·3⟩ ; lem-nat-0-SBOX⟨1·0·42·3⟩ ; lem-nat-1-SBOX⟨1·0·42·3⟩ ; lem-nat-1-SBOX⟨2·0·41·3⟩ ; lem-nat-2-CS02 ; lem-nat-2-CSd02 ; lem-nat-2-SBOX⟨0·1·23·4⟩ ; lem-nat-2-SBOX⟨0·1·32·4⟩ ; lem-nat-3-SBOX⟨0·1·32·4⟩ ; lem-nat-3-SBOX⟨0·1·42·3⟩)
open import Examples.Groups.Clifford+CS.Five.D.R016 using (lem-nat-3-CS04 ; lem-nat-3-CSd04)
open import Examples.Groups.Clifford+CS.Five.D.R017 using (lem-nat-2-CS04 ; lem-nat-2-CSd04 ; lem-nat-3-CS03 ; lem-nat-3-CSd03)
open import Examples.Groups.Clifford+CS.Five.D.R019 using (lem-nat-2-CS03 ; lem-nat-2-CSd03 ; lem-nat-2-CX20 ; lem-nat-2-CX30)
open import Examples.Groups.Clifford+CS.Five.D.R025 using (lem-nat-0-BOX⟨1·4203⟩ ; lem-nat-1-BOX⟨0·4213⟩)
open import Examples.Groups.Clifford+CS.Five.D.R028 using (lem-nat-1-BOX⟨3·0421⟩)
open import Examples.Groups.Clifford+CS.Five.D.R030 using (lem-comm-SBOXd⟨0·1·2·3⟩-TOFF403)
open import Examples.Groups.Clifford+CS.Five.D.R032 using (lem-nat-0-BOX⟨3·1402⟩ ; lem-nat-0-BOX⟨3·1420⟩)
open import Examples.Groups.Clifford+CS.Five.D.R036 using (lem-nat-2-SBOX⟨2·1·4·0⟩ ; lem-nat-2-SBOX⟨3·1·4·0⟩ ; lem-nat-3-SBOX⟨2·1·3·0⟩ ; lem-nat-3-SBOX⟨2·1·4·0⟩)
-- F4 CS01^0|CS01^1: 63 steps
lem-F4-CS01ᵖ0∣CS01ᵖ1 : Complete 4 → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS01ᵖ0∣CS01ᵖ1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (CS01 ∷ CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ Toff204 ∷ CCZ024 ∷ [])
  b0 = at 0 4 (CS01 ∷ []) (lem-F5-CS01 c4) ▸
       at 1 0 (CCZ024 ∷ CCZ024 ∷ []) (pw1 c4 [] (CCZ024 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 2 0 (Toff204 ∷ Toff204 ∷ []) (pw1 c4 [] (Toff204 ∷ Toff204 ∷ []) tt tt Eq.refl) ▸
       at 3 0 (CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ []) (lw4 c4 [] (CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Bx2-03 ∷ []) (refl) ▸
       at 8 1 (Bx2-03 ∷ []) (refl) ▸
       at 3 6 (Bx0-213 ∷ []) (refl) ▸
       at 4 1 (Bx⁻2-03 ∷ []) (refl) ▸ done

  b1 : Chain (CS01 ∷ CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ Toff204 ∷ CCZ024 ∷ []) (CS01 ∷ CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CCZ024 ∷ Toff204 ∷ Bx⁻0-213 ∷ Toff204 ∷ CCZ024 ∷ [])
  b1 = at 7 1 (Bx⁻2-03 ∷ []) (refl) ▸
       at 4 6 (Bx⁻0-213 ∷ []) (refl) ▸
       at 4 0 (Toff204 ∷ Toff204 ∷ []) (pw1 c4 [] (Toff204 ∷ Toff204 ∷ []) tt tt Eq.refl) ▸
       at 5 0 (CCZ024 ∷ CCZ024 ∷ []) (pw1 c4 [] (CCZ024 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 6 0 (CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ []) (lw4 c4 [] (CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 8 1 (Bx2-03 ∷ []) (refl) ▸
       at 11 1 (Bx2-03 ∷ []) (refl) ▸
       at 6 6 (Bx0-213 ∷ []) (refl) ▸ done

  b2 : Chain (CS01 ∷ CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CCZ024 ∷ Toff204 ∷ Bx⁻0-213 ∷ Toff204 ∷ CCZ024 ∷ []) (CS01 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ CS03⁻ ∷ Toff314 ∷ Bx⁻2-0413 ∷ [])
  b2 = at 7 1 (Bx⁻2-03 ∷ []) (refl) ▸
       at 10 1 (Bx⁻2-03 ∷ []) (refl) ▸
       at 7 6 (Bx⁻0-213 ∷ []) (refl) ▸
       at 1 6 (Bx2-0413 ∷ []) (refl) ▸
       at 2 6 (Bx⁻2-0413 ∷ []) (refl) ▸
       at 2 0 (Toff314 ∷ Toff314 ∷ []) (lw0 c4 [] (Toff314 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 3 0 (CS03 ∷ CS03⁻ ∷ []) (lw4 c4 [] (CS03 ∷ CS03⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb2-0-3-1 ∷ []) (refl) ▸ done

  b3 : Chain (CS01 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ CS03⁻ ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) (Sb2-0-41-3 ∷ CS01 ∷ Sb⁻2-0-41-3 ∷ [])
  b3 = at 4 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 4 0 (Toff314 ∷ Toff314 ∷ []) (lw0 c4 [] (Toff314 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 5 0 (CS03⁻ ∷ CS03 ∷ []) (lw4 c4 [] (CS03⁻ ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 6 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 1 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 2 5 (Sb⁻2-0-41-3 ∷ []) (refl) ▸
       at 0 2 (Sb2-0-41-3 ∷ CS01 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at3443 c4) ▸ done

  b4 : Chain (Sb2-0-41-3 ∷ CS01 ∷ Sb⁻2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ [])
  b4 = at 1 1 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F5-CS01 c4)) ▸
       at 5 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) (refl) ▸
       at 4 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 8 1 (CS03⁻ ∷ []) (refl) ▸
       at 9 1 (CS03 ∷ []) (refl) ▸
       at 8 2 [] (lw4 c4 (CS03⁻ ∷ CS03 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 [] (lw0 c4 (Toff314 ∷ Toff314 ∷ []) [] tt tt Eq.refl) ▸
       at 6 1 (CS03 ∷ []) (refl) ▸ done

  b5 : Chain (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ Bx⁻0-213 ∷ CCZ024 ∷ Toff204 ∷ Bx⁻0-213 ∷ Toff204 ∷ CCZ024 ∷ [])
  b5 = at 7 1 (CS03⁻ ∷ []) (refl) ▸
       at 6 2 [] (lw4 c4 (CS03 ∷ CS03⁻ ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 [] (lw0 c4 (Toff314 ∷ Toff314 ∷ []) [] tt tt Eq.refl) ▸
       at 5 1 (Bx⁻0-213 ∷ CCZ024 ∷ Toff204 ∷ Bx⁻0-213 ∷ Toff204 ∷ CCZ024 ∷ []) (refl) ▸
       at 4 1 (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ []) (refl) ▸
       at 9 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) (refl) ▸
       at 11 1 (CZ03 ∷ []) (refl) ▸
       at 14 1 (CZ03 ∷ []) (refl) ▸ done

  b6 : Chain (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ Bx⁻0-213 ∷ CCZ024 ∷ Toff204 ∷ Bx⁻0-213 ∷ Toff204 ∷ CCZ024 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CCZ024 ∷ Toff204 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ Bx⁻0-213 ∷ Toff204 ∷ CCZ024 ∷ [])
  b6 = at 15 1 (Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ []) (refl) ▸
       at 15 1 (CZ03 ∷ []) (refl) ▸
       at 18 1 (CZ03 ∷ []) (refl) ▸
       at 9 12 [] (lw4 c4 (CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 [] (pw1 c4 (CCZ024 ∷ CCZ024 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 [] (pw1 c4 (Toff204 ∷ Toff204 ∷ []) [] tt tt Eq.refl) ▸
       at 6 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) (refl) ▸
       at 8 1 (CZ03 ∷ []) (refl) ▸ done

  b7 : Chain (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CCZ024 ∷ Toff204 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ Bx⁻0-213 ∷ Toff204 ∷ CCZ024 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b7 = at 11 1 (CZ03 ∷ []) (refl) ▸
       at 12 1 (Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ []) (refl) ▸
       at 12 1 (CZ03 ∷ []) (refl) ▸
       at 15 1 (CZ03 ∷ []) (refl) ▸
       at 6 12 [] (lw4 c4 (CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 [] (pw1 c4 (Toff204 ∷ Toff204 ∷ []) [] tt tt Eq.refl) ▸
       at 4 2 [] (pw1 c4 (CCZ024 ∷ CCZ024 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CSd23: 5 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd23 : Complete 4 → ⟪ (Bx0-1234 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd23 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Bx0-1234 ∷ [])
  b0 = at 0 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 0 1 (Bx0-2314 ∷ []) (lem-sym23-at1221 c4) ▸
       at 0 2 (CS23⁻ ∷ Bx0-2314 ∷ []) (sym (lem-CSd12-beta-at122331 c4)) ▸
       at 1 1 (Bx0-2134 ∷ []) (lem-sym23-at122331 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸ done


-- auto SBOX(0;1;23;4) | CS13: 11 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS13 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS13 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-23-4 ∷ CS13 ∷ []) (Bx0-1234 ∷ Toff423 ∷ CS13 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 1 (CS14⁻ ∷ []) (refl) ▸
       at 4 2 (CS13 ∷ CS14⁻ ∷ []) (lw0 c4 (CS14⁻ ∷ CS13 ∷ []) (CS13 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 3 2 (CS13 ∷ Toff423 ∷ []) (lw0 c4 (Toff423 ∷ CS13 ∷ []) (CS13 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CS14 ∷ []) (refl) ▸
       at 2 2 (CS13 ∷ CS14 ∷ []) (lw0 c4 (CS14 ∷ CS13 ∷ []) (CS13 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb0-1-4-3 ∷ []) (refl) ▸ done

  b1 : Chain (Bx0-1234 ∷ Toff423 ∷ CS13 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (CS13 ∷ Sb0-1-23-4 ∷ [])
  b1 = at 1 2 (CS13 ∷ Toff423 ∷ []) (lw0 c4 (Toff423 ∷ CS13 ∷ []) (CS13 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (CS13 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS13 c4) ▸
       at 1 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- auto BOX(0;1234) | CSd23 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd23-at2332 : Complete 4 → ⟪ (Bx0-1324 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd23-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ c4) ▸
       at 2 2 (CS23⁻ ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS23⁻ ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd23 c4) ▸
       at 0 2 (CS23⁻ ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CS13 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS13-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS13-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CS12 ∷ []) (CS12 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (CS13 ∷ Sw23 ∷ []) (lem-nat-2-CS12 c4) ▸
       at 1 2 (CS13 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS13 c4) ▸
       at 0 2 (CS12 ∷ Sw23 ∷ []) (lem-nat-2-CS13 c4) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CCZ213: 34 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ213 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ213 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (run b4))))
  where
  b0 : Chain (Sb0-1-23-4 ∷ CCZ123 ∷ []) (CS23 ∷ Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS12 ∷ [])
  b0 = at 1 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS23 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS23-at2332 c4) ▸
       at 1 1 (Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ []) (refl) ▸
       at 5 1 (CS14⁻ ∷ []) (refl) ▸
       at 5 4 (CX13 ∷ CS23⁻ ∷ CX13 ∷ CS14⁻ ∷ []) (lw0 c4 (CS14⁻ ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ []) (CX13 ∷ CS23⁻ ∷ CX13 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 8 1 (Sb⁻0-1-4-2 ∷ []) (refl) ▸
       at 4 4 (CX13 ∷ CS23⁻ ∷ CX13 ∷ Toff423 ∷ []) (lw0 c4 (Toff423 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ []) (CX13 ∷ CS23⁻ ∷ CX13 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CS23 ∷ Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS12 ∷ []) (CS23 ∷ CX13 ∷ Bx0-2134 ∷ CCZ124 ∷ CS23⁻ ∷ CX13 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS12 ∷ [])
  b1 = at 3 1 (CS14 ∷ []) (refl) ▸
       at 3 4 (CX13 ∷ CS23⁻ ∷ CX13 ∷ CS14 ∷ []) (lw0 c4 (CS14 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ []) (CX13 ∷ CS23⁻ ∷ CX13 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sb0-1-4-2 ∷ []) (refl) ▸
       at 2 4 (CX13 ∷ CS23⁻ ∷ CX13 ∷ Toff423 ∷ []) (lw0 c4 (Toff423 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ []) (CX13 ∷ CS23⁻ ∷ CX13 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 1 0 (CX13 ∷ CX13 ∷ []) (lw4 c4 [] (CX13 ∷ CX13 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸
       at 3 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 2 3 (Bx0-2134 ∷ CCZ124 ∷ []) (lem-CX23-beta-at1221 c4) ▸ done

  b2 : Chain (CS23 ∷ CX13 ∷ Bx0-2134 ∷ CCZ124 ∷ CS23⁻ ∷ CX13 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS12 ∷ []) (CS23 ∷ CX13 ∷ CCZ124 ∷ CS23⁻ ∷ CX13 ∷ Bx0-2134 ∷ CCZ124 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS12 ∷ [])
  b2 = at 2 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸
       at 2 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 2 2 (CCZ124 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ314-at2332 c4) ▸
       at 3 2 (CS23⁻ ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd23-at2332 c4) ▸
       at 4 0 (CX13 ∷ CX13 ∷ []) (lw4 c4 [] (CX13 ∷ CX13 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸
       at 6 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 5 3 (Bx0-2134 ∷ CCZ124 ∷ []) (lem-CX23-beta-at1221 c4) ▸ done

  b3 : Chain (CS23 ∷ CX13 ∷ CCZ124 ∷ CS23⁻ ∷ CX13 ∷ Bx0-2134 ∷ CCZ124 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS12 ∷ []) (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ Sb0-1-32-4 ∷ [])
  b3 = at 5 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸
       at 5 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 5 2 (CCZ124 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ314-at2332 c4) ▸
       at 1 2 (CCZ124 ∷ CX13 ∷ []) (lw0 c4 (CX13 ∷ CCZ124 ∷ []) (CCZ124 ∷ CX13 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (CCZ124 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ []) (lw0 c4 (CX13 ∷ CS23⁻ ∷ CX13 ∷ CCZ124 ∷ []) (CCZ124 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ []) tt tt Eq.refl) ▸
       at 1 2 [] (lw0 c4 (CCZ124 ∷ CCZ124 ∷ []) [] tt tt Eq.refl) ▸
       at 4 5 (Sb0-1-32-4 ∷ []) (refl) ▸
       at 4 2 (CS12 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS13-at2332 c4) ▸ done

  b4 : Chain (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ Sb0-1-32-4 ∷ []) (CCZ123 ∷ Sb0-1-23-4 ∷ [])
  b4 = at 5 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 5 (CCZ123 ∷ []) (lw4 c4 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CS10 CS10: 6 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS10-CS10 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CS01 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS10-CS10 c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ CS01 ∷ CS01 ∷ []) (CS01 ∷ CS01 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS01 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS10-at2332 c4) ▸
       at 1 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 1 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 1 2 (CS01 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS10-at2332 c4) ▸
       at 2 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸ done


-- auto SBOX(0;1;23;4) | CS10 CS10 @2332: 9 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS10-CS10-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CS01 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS10-CS10-at2332 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-32-4 ∷ CS01 ∷ CS01 ∷ []) (CS01 ∷ CS01 ∷ Sb0-1-32-4 ∷ Sw23 ∷ Sw23 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (CS01 ∷ Sw23 ∷ []) (sym (c₂ (CS) (Swap))) ▸
       at 3 2 (CS01 ∷ Sw23 ∷ []) (sym (c₂ (CS) (Swap))) ▸
       at 1 3 (CS01 ∷ CS01 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS10-CS10 c4) ▸
       at 0 2 (CS01 ∷ Sw23 ∷ []) (sym (c₂ (CS) (Swap))) ▸
       at 1 2 (CS01 ∷ Sw23 ∷ []) (sym (c₂ (CS) (Swap))) ▸
       at 2 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸ done

  b1 : Chain (CS01 ∷ CS01 ∷ Sb0-1-32-4 ∷ Sw23 ∷ Sw23 ∷ []) (CS01 ∷ CS01 ∷ Sb0-1-32-4 ∷ [])
  b1 = at 3 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CZ10: 5 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CZ10 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CZ01 ∷ []) ⟫ʷ ≈ ⟪ (CZ01 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CZ10 c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ CZ01 ∷ []) (CZ01 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 1 1 (CS01 ∷ CS01 ∷ []) (lw4 c4 (CZ01 ∷ []) (CS01 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 3 (CS01 ∷ CS01 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS10-CS10-at2332 c4) ▸
       at 2 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 2 (CZ01 ∷ []) (lw4 c4 (CS01 ∷ CS01 ∷ []) (CZ01 ∷ []) tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CZ10 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CZ10-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ CZ01 ∷ []) ⟫ʷ ≈ ⟪ (CZ01 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CZ10-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CZ01 ∷ []) (CZ01 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (CZ01 ∷ Sw23 ∷ []) (sym (c₂ (CZ) (Swap))) ▸
       at 1 2 (CZ01 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CZ10 c4) ▸
       at 0 2 (CZ01 ∷ Sw23 ∷ []) (sym (c₂ (CZ) (Swap))) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CX10: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CX10 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CX10 ∷ []) ⟫ʷ ≈ ⟪ (CX10 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CX10 c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ CX10 ∷ []) (CX10 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 1 1 (K0 ∷ CZ01 ∷ K0⁻ ∷ []) (lw4 c4 (CX10 ∷ []) (K0 ∷ CZ01 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (K0 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at2332 c4) ▸
       at 1 2 (CZ01 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CZ10-at2332 c4) ▸
       at 2 2 (K0⁻ ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd0-at2332 c4) ▸
       at 3 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 3 (CX10 ∷ []) (lw4 c4 (K0 ∷ CZ01 ∷ K0⁻ ∷ []) (CX10 ∷ []) tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CS03 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS03-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS03-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CS02 ∷ []) (CS02 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (CS03 ∷ Sw23 ∷ []) (lem-nat-2-CS02 c4) ▸
       at 1 2 (CS03 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS03 c4) ▸
       at 0 2 (CS02 ∷ Sw23 ∷ []) (lem-nat-2-CS03 c4) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CX10 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CX10-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ CX10 ∷ []) ⟫ʷ ≈ ⟪ (CX10 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CX10-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CX10 ∷ []) (CX10 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (CX10 ∷ Sw23 ∷ []) (sym (c₂ (CX₁₀) (Swap))) ▸
       at 1 2 (CX10 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CX10 c4) ▸
       at 0 2 (CX10 ∷ Sw23 ∷ []) (sym (c₂ (CX₁₀) (Swap))) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CCZ210: 9 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ210 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ210 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-23-4 ∷ CCZ012 ∷ []) (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 1 1 (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS02 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS03-at2332 c4) ▸
       at 1 2 (CX10 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CX10-at2332 c4) ▸
       at 2 2 (CS02⁻ ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd03-at2332 c4) ▸
       at 3 2 (CX10 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CX10-at2332 c4) ▸
       at 4 2 (CS12 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS13-at2332 c4) ▸
       at 5 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸ done

  b1 : Chain (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Sb0-1-23-4 ∷ []) (CCZ012 ∷ Sb0-1-23-4 ∷ [])
  b1 = at 0 5 (CCZ012 ∷ []) (lw4 c4 (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CCZ214: 9 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ214 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ214 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-23-4 ∷ CCZ124 ∷ []) (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 1 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (lw0 c4 (CCZ124 ∷ []) (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS24 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS43-at2332 c4) ▸
       at 1 2 (CX14 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CX14-at2332 c4) ▸
       at 2 2 (CS24⁻ ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd43-at2332 c4) ▸
       at 3 2 (CX14 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CX14-at2332 c4) ▸
       at 4 2 (CS12 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS13-at2332 c4) ▸
       at 5 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸ done

  b1 : Chain (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Sb0-1-23-4 ∷ []) (CCZ124 ∷ Sb0-1-23-4 ∷ [])
  b1 = at 0 5 (CCZ124 ∷ []) (lw0 c4 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ341: 5 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ341 : Complete 4 → ⟪ (Bx0-1234 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ341 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CCZ134 ∷ []) (CCZ134 ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ []) (lw0 c4 (CCZ134 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 0 2 (CCZ134 ∷ Bx0-1324 ∷ []) (sym (lem-c124-beta-at2332 c4)) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸
       at 0 1 (CCZ134 ∷ []) (lw0 c4 (CCZ134 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;2;3) | TOFF430: 1 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-TOFF430 : Complete 4 → ⟪ (Sb⁻0-1-2-3 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ Sb⁻0-1-2-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-TOFF430 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-2-3 ∷ Toff403 ∷ []) (Toff403 ∷ Sb⁻0-1-2-3 ∷ [])
  b0 = at 0 2 (Toff403 ∷ Sb⁻0-1-2-3 ∷ []) (lem-comm-SBOXd⟨0·1·2·3⟩-TOFF403 c4) ▸ done


-- auto SBOX(0;1;23;4) | CX20 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CX20-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ CX30 ∷ []) ⟫ʷ ≈ ⟪ (CX30 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CX20-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CX30 ∷ []) (CX30 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (CX20 ∷ Sw23 ∷ []) (lem-nat-2-CX30 c4) ▸
       at 1 2 (CX20 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CX20 c4) ▸
       at 0 2 (CX30 ∷ Sw23 ∷ []) (lem-nat-2-CX20 c4) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CCZ230: 9 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ230 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ230 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-23-4 ∷ CCZ023 ∷ []) (CS02 ∷ CX30 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 1 1 (CS02 ∷ CX30 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ []) (lw4 c4 (CCZ023 ∷ []) (CS02 ∷ CX30 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS02 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS03-at2332 c4) ▸
       at 1 2 (CX30 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CX20-at2332 c4) ▸
       at 2 2 (CS02⁻ ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd03-at2332 c4) ▸
       at 3 2 (CX30 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CX20-at2332 c4) ▸
       at 4 2 (CS23 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS23-at2332 c4) ▸
       at 5 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸ done

  b1 : Chain (CS02 ∷ CX30 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ Sb0-1-23-4 ∷ []) (CCZ023 ∷ Sb0-1-23-4 ∷ [])
  b1 = at 0 5 (CCZ023 ∷ []) (lw4 c4 (CS02 ∷ CX30 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸ done


-- beta-T @03243042: 8 steps
lem-beta-T-at03243042 : Complete 4 → ⟪ (Bx3-1402 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ []) ⟫ʷ
lem-beta-T-at03243042 c4 = run b0
  where
  b0 : Chain (Bx3-1402 ∷ []) (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-0412 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1402⟩ c4) ▸
       at 1 1 (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-beta-T-at0310243142 c4) ▸
       at 0 2 (Toff314 ∷ Sw01 ∷ []) (lem-nat-0-TOFF304 c4) ▸
       at 1 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff314 ∷ Sw01 ∷ []) (lem-nat-0-TOFF304 c4) ▸
       at 3 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(3;1402): 14 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨3·1402⟩ : Complete 4 → ⟪ (Sb⁻0-1-2-3 ∷ Bx3-1402 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1402 ∷ Sb⁻0-1-2-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨3·1402⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb⁻0-1-2-3 ∷ Bx3-1402 ∷ []) (Toff314 ∷ CCZ023 ∷ CS12⁻ ∷ Toff314 ∷ CCZ023 ∷ [])
  b0 = at 1 1 (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ []) (lem-beta-T-at03243042 c4) ▸
       at 0 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 2 (Toff314 ∷ CS12⁻ ∷ []) (lw0 c4 (CS12⁻ ∷ Toff314 ∷ []) (Toff314 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 1 1 (CS12⁻ ∷ []) (refl) ▸
       at 1 2 (CCZ023 ∷ CS12⁻ ∷ []) (lw4 c4 (CS12⁻ ∷ CCZ023 ∷ []) (CCZ023 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 2 1 (CS12⁻ ∷ []) (refl) ▸ done

  b1 : Chain (Toff314 ∷ CCZ023 ∷ CS12⁻ ∷ Toff314 ∷ CCZ023 ∷ []) (Bx3-1402 ∷ Sb⁻0-1-2-3 ∷ [])
  b1 = at 2 2 (Toff314 ∷ CS12⁻ ∷ []) (lw0 c4 (CS12⁻ ∷ Toff314 ∷ []) (Toff314 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 3 1 (CS12⁻ ∷ []) (refl) ▸
       at 3 2 (CCZ023 ∷ CS12⁻ ∷ []) (lw4 c4 (CS12⁻ ∷ CCZ023 ∷ []) (CCZ023 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 0 4 (Bx3-1402 ∷ []) (sym (lem-beta-T-at03243042 c4)) ▸ done


-- beta-T @0310243241: 8 steps
lem-beta-T-at0310243241 : Complete 4 → ⟪ (Bx3-0421 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) ⟫ʷ
lem-beta-T-at0310243241 c4 = run b0
  where
  b0 : Chain (Bx3-0421 ∷ []) (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-0412 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0421⟩ c4) ▸
       at 1 1 (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-beta-T-at0310243142 c4) ▸
       at 0 2 (Toff304 ∷ Sw12 ∷ []) (lem-nat-1-TOFF304 c4) ▸
       at 1 2 (CCZ123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff304 ∷ Sw12 ∷ []) (lem-nat-1-TOFF304 c4) ▸
       at 3 2 (CCZ123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- beta-T @03243240: 8 steps
lem-beta-T-at03243240 : Complete 4 → ⟪ (Bx3-1420 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ []) ⟫ʷ
lem-beta-T-at03243240 c4 = run b0
  where
  b0 : Chain (Bx3-1420 ∷ []) (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-0421 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1420⟩ c4) ▸
       at 1 1 (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-beta-T-at0310243241 c4) ▸
       at 0 2 (Toff314 ∷ Sw01 ∷ []) (lem-nat-0-TOFF304 c4) ▸
       at 1 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff314 ∷ Sw01 ∷ []) (lem-nat-0-TOFF304 c4) ▸
       at 3 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(3;1420): 14 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨3·1420⟩ : Complete 4 → ⟪ (Sb⁻0-1-2-3 ∷ Bx3-1420 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1420 ∷ Sb⁻0-1-2-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨3·1420⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb⁻0-1-2-3 ∷ Bx3-1420 ∷ []) (Toff314 ∷ CCZ023 ∷ CS12⁻ ∷ Toff314 ∷ CCZ023 ∷ [])
  b0 = at 1 1 (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ []) (lem-beta-T-at03243240 c4) ▸
       at 0 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 2 (Toff314 ∷ CS12⁻ ∷ []) (lw0 c4 (CS12⁻ ∷ Toff314 ∷ []) (Toff314 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 1 1 (CS12⁻ ∷ []) (refl) ▸
       at 1 2 (CCZ023 ∷ CS12⁻ ∷ []) (lw4 c4 (CS12⁻ ∷ CCZ023 ∷ []) (CCZ023 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 2 1 (CS12⁻ ∷ []) (refl) ▸ done

  b1 : Chain (Toff314 ∷ CCZ023 ∷ CS12⁻ ∷ Toff314 ∷ CCZ023 ∷ []) (Bx3-1420 ∷ Sb⁻0-1-2-3 ∷ [])
  b1 = at 2 2 (Toff314 ∷ CS12⁻ ∷ []) (lw0 c4 (CS12⁻ ∷ Toff314 ∷ []) (Toff314 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 3 1 (CS12⁻ ∷ []) (refl) ▸
       at 3 2 (CCZ023 ∷ CS12⁻ ∷ []) (lw4 c4 (CS12⁻ ∷ CCZ023 ∷ []) (CCZ023 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 0 4 (Bx3-1420 ∷ []) (sym (lem-beta-T-at03243240 c4)) ▸ done


-- auto CCZ012 | TOFF314: 5 steps
lem-auto-CCZ012-∣-TOFF314 : Complete 4 → ⟪ (CCZ012 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-TOFF314 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Toff314 ∷ []) (Toff314 ∷ CCZ012 ∷ [])
  b0 = at 1 1 (K3 ∷ CCZ134 ∷ K3⁻ ∷ []) (lw0 c4 (Toff314 ∷ []) (K3 ∷ CCZ134 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 0 2 (K3 ∷ CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ K3 ∷ []) (K3 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ134 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-CCZ314 c4) ▸
       at 2 2 (K3⁻ ∷ CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ K3⁻ ∷ []) (K3⁻ ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Toff314 ∷ []) (lw0 c4 (K3 ∷ CCZ134 ∷ K3⁻ ∷ []) (Toff314 ∷ []) tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CSd02: 1 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd02 : Complete 4 → ⟪ (Bx0-1234 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd02 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ Bx0-1234 ∷ [])
  b0 = at 0 2 (CS02⁻ ∷ Bx0-1234 ∷ []) (sym (lem-CS20-beta-ci c4)) ▸ done


-- auto SBOX(0;1;23;4) | CSd02: 11 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd02 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd02 c4 = trans (run b0) (run b1)
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
       at 0 2 (CS02⁻ ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd02 c4) ▸
       at 1 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- auto SBOX(0;1;23;4) | CSd02 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd02-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd02-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (CS02⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd03 c4) ▸
       at 1 2 (CS02⁻ ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd02 c4) ▸
       at 0 2 (CS03⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd02 c4) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CCZ310: 9 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ310 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ310 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-23-4 ∷ CCZ013 ∷ []) (CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 1 1 (CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ []) (lw4 c4 (CCZ013 ∷ []) (CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS03 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS02-at2332 c4) ▸
       at 1 2 (CX10 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CX10-at2332 c4) ▸
       at 2 2 (CS03⁻ ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd02-at2332 c4) ▸
       at 3 2 (CX10 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CX10-at2332 c4) ▸
       at 4 2 (CS13 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS12-at2332 c4) ▸
       at 5 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸ done

  b1 : Chain (CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ Sb0-1-23-4 ∷ []) (CCZ013 ∷ Sb0-1-23-4 ∷ [])
  b1 = at 0 5 (CCZ013 ∷ []) (lw4 c4 (CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CS04: 5 steps
lem-auto-BOX⟨0·1234⟩-∣-CS04 : Complete 4 → ⟪ (Bx0-1234 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS04 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CS04 ∷ []) (CS04 ∷ Bx0-1234 ∷ [])
  b0 = at 0 1 (Bx0-1243 ∷ []) (lem-sym34 c4) ▸
       at 0 1 (Bx0-1423 ∷ []) (lem-sym23-at3443 c4) ▸
       at 0 2 (CS04 ∷ Bx0-1423 ∷ []) (sym (lem-CS20-beta-c-at243243 c4)) ▸
       at 1 1 (Bx0-1243 ∷ []) (lem-sym23-at243243 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym34-at3443 c4) ▸ done


-- auto BOX(0;1234) | CSd04: 5 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd04 : Complete 4 → ⟪ (Bx0-1234 ∷ CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS04⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd04 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ Bx0-1234 ∷ [])
  b0 = at 0 1 (Bx0-1243 ∷ []) (lem-sym34 c4) ▸
       at 0 1 (Bx0-1423 ∷ []) (lem-sym23-at3443 c4) ▸
       at 0 2 (CS04⁻ ∷ Bx0-1423 ∷ []) (sym (lem-CS20-beta-ci-at243243 c4)) ▸
       at 1 1 (Bx0-1243 ∷ []) (lem-sym23-at243243 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym34-at3443 c4) ▸ done


-- auto SBOX(0;1;23;4) | SBOX(3;1;4;0): 5 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨3·1·4·0⟩ : Complete 4 → ⟪ (Sb0-1-23-4 ∷ Sb3-1-4-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-1-4-0 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨3·1·4·0⟩ c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ Sb3-1-4-0 ∷ []) (Sb3-1-4-0 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 1 1 (CS14 ∷ []) (refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS14 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS14-at2332 c4) ▸
       at 1 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 1 (Sb3-1-4-0 ∷ []) (refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOXd(3;1;4;0): 5 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨3·1·4·0⟩ : Complete 4 → ⟪ (Sb0-1-23-4 ∷ Sb⁻3-1-4-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-1-4-0 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨3·1·4·0⟩ c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ Sb⁻3-1-4-0 ∷ []) (Sb⁻3-1-4-0 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 1 1 (CS14⁻ ∷ []) (refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS14⁻ ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd14-at2332 c4) ▸
       at 1 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 1 (Sb⁻3-1-4-0 ∷ []) (refl) ▸ done


-- beta-T @143143: 8 steps
lem-beta-T-at143143 : Complete 4 → ⟪ (Bx0-4213 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) ⟫ʷ
lem-beta-T-at143143 c4 = run b0
  where
  b0 : Chain (Bx0-4213 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-4123 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·4213⟩ c4) ▸
       at 1 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at14213243 c4) ▸
       at 0 2 (Toff024 ∷ Sw12 ∷ []) (lem-nat-1-TOFF014 c4) ▸
       at 1 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 2 2 (Toff024 ∷ Sw12 ∷ []) (lem-nat-1-TOFF014 c4) ▸
       at 3 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 4 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- beta-T @01143043: 8 steps
lem-beta-T-at01143043 : Complete 4 → ⟪ (Bx1-4203 ∷ []) ⟫ʷ ≈ ⟪ (Toff124 ∷ CCZ013 ∷ Toff124 ∷ CCZ013 ∷ []) ⟫ʷ
lem-beta-T-at01143043 c4 = run b0
  where
  b0 : Chain (Bx1-4203 ∷ []) (Toff124 ∷ CCZ013 ∷ Toff124 ∷ CCZ013 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-4213 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·4203⟩ c4) ▸
       at 1 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-beta-T-at143143 c4) ▸
       at 0 2 (Toff124 ∷ Sw01 ∷ []) (lem-nat-0-TOFF024 c4) ▸
       at 1 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff124 ∷ Sw01 ∷ []) (lem-nat-0-TOFF024 c4) ▸
       at 3 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CCZ314 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ314-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ314-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 1 2 (CCZ134 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ314 c4) ▸
       at 0 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CCZ314 @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ314-at243243 : Complete 4 → ⟪ (Sb0-1-42-3 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ314-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ c4) ▸
       at 2 2 (CCZ124 ∷ Sw34 ∷ []) (lem-nat-3-CCZ123 c4) ▸
       at 1 2 (CCZ124 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ314-at2332 c4) ▸
       at 0 2 (CCZ123 ∷ Sw34 ∷ []) (lem-nat-3-CCZ124 c4) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CCZ314 @0110243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ314-at0110243243 : Complete 4 → ⟪ (Sb1-0-42-3 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ314-at0110243243 c4 = run b0
  where
  b0 : Chain (Sb1-0-42-3 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sb1-0-42-3 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ c4) ▸
       at 2 2 (CCZ123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ023 ∷ []) (CCZ123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ123 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ314-at243243 c4) ▸
       at 0 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CCZ314 @0210243143: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ314-at0210243143 : Complete 4 → ⟪ (Sb2-0-41-3 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ314-at0210243143 c4 = run b0
  where
  b0 : Chain (Sb2-0-41-3 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sb2-0-41-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ c4) ▸
       at 2 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 1 2 (CCZ023 ∷ Sb1-0-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ314-at0110243243 c4) ▸
       at 0 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 1 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @01143043: 5 steps
lem-sym23-at01143043 : Complete 4 → ⟪ (Bx1-4203 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-4023 ∷ []) ⟫ʷ
lem-sym23-at01143043 c4 = run b0
  where
  b0 : Chain (Bx1-4203 ∷ []) (Bx1-4023 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-4213 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·4203⟩ c4) ▸
       at 1 1 (Bx0-4123 ∷ []) (lem-sym23-at143143 c4) ▸
       at 0 2 (Bx1-4023 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·4123⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CS04 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS04-at2332 : Complete 4 → ⟪ (Bx0-1324 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS04-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ CS04 ∷ []) (CS04 ∷ Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ c4) ▸
       at 2 2 (CS04 ∷ Sw23 ∷ []) (lem-nat-2-CS04 c4) ▸
       at 1 2 (CS04 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS04 c4) ▸
       at 0 2 (CS04 ∷ Sw23 ∷ []) (lem-nat-2-CS04 c4) ▸
       at 1 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CS04 @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS04-at243243 : Complete 4 → ⟪ (Bx0-1423 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS04-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ CS03 ∷ []) (CS03 ∷ Bx0-1423 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ c4) ▸
       at 2 2 (CS04 ∷ Sw34 ∷ []) (lem-nat-3-CS03 c4) ▸
       at 1 2 (CS04 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS04-at2332 c4) ▸
       at 0 2 (CS03 ∷ Sw34 ∷ []) (lem-nat-3-CS04 c4) ▸
       at 1 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CS04 @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS04-at0110243243 : Complete 4 → ⟪ (Bx1-0423 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS04-at0110243243 c4 = run b0
  where
  b0 : Chain (Bx1-0423 ∷ CS13 ∷ []) (CS13 ∷ Bx1-0423 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ c4) ▸
       at 2 2 (CS03 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS13 ∷ []) (CS03 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS03 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS04-at243243 c4) ▸
       at 0 2 (CS13 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS03 ∷ []) (CS13 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CS04 @0210243143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS04-at0210243143 : Complete 4 → ⟪ (Bx2-0413 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS04-at0210243143 c4 = run b0
  where
  b0 : Chain (Bx2-0413 ∷ CS23 ∷ []) (CS23 ∷ Bx2-0413 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ c4) ▸
       at 2 2 (CS13 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS23 ∷ []) (CS13 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS13 ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS04-at0110243243 c4) ▸
       at 0 2 (CS23 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS13 ∷ []) (CS23 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | K0 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-K0-at2332 : Complete 4 → ⟪ (Bx0-1324 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-K0-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ K0 ∷ []) (K0 ∷ Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ c4) ▸
       at 2 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 1 2 (K0 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-K0 c4) ▸
       at 0 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 1 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | K0 @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-K0-at243243 : Complete 4 → ⟪ (Bx0-1423 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-K0-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ K0 ∷ []) (K0 ∷ Bx0-1423 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ c4) ▸
       at 2 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 1 2 (K0 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-K0-at2332 c4) ▸
       at 0 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 1 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | K0 @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-K0-at0110243243 : Complete 4 → ⟪ (Bx1-0423 ∷ K1 ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-K0-at0110243243 c4 = run b0
  where
  b0 : Chain (Bx1-0423 ∷ K1 ∷ []) (K1 ∷ Bx1-0423 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ c4) ▸
       at 2 2 (K0 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ K1 ∷ []) (K0 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (K0 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-K0-at243243 c4) ▸
       at 0 2 (K1 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ K0 ∷ []) (K1 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | K0 @0210243143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-K0-at0210243143 : Complete 4 → ⟪ (Bx2-0413 ∷ K2 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-K0-at0210243143 c4 = run b0
  where
  b0 : Chain (Bx2-0413 ∷ K2 ∷ []) (K2 ∷ Bx2-0413 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ c4) ▸
       at 2 2 (K1 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ K2 ∷ []) (K1 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (K1 ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-K0-at0110243243 c4) ▸
       at 0 2 (K2 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ K1 ∷ []) (K2 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | Kd0 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-Kd0-at2332 : Complete 4 → ⟪ (Bx0-1324 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-Kd0-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ K0⁻ ∷ []) (K0⁻ ∷ Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ c4) ▸
       at 2 2 (K0⁻ ∷ Sw23 ∷ []) (sym (c₁ (K • iI) (Swap ↑))) ▸
       at 1 2 (K0⁻ ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-Kd0 c4) ▸
       at 0 2 (K0⁻ ∷ Sw23 ∷ []) (sym (c₁ (K • iI) (Swap ↑))) ▸
       at 1 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | Kd0 @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-Kd0-at243243 : Complete 4 → ⟪ (Bx0-1423 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-Kd0-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ K0⁻ ∷ []) (K0⁻ ∷ Bx0-1423 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ c4) ▸
       at 2 2 (K0⁻ ∷ Sw34 ∷ []) (sym (c₁ (K • iI) (Swap ↑ ↑))) ▸
       at 1 2 (K0⁻ ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-Kd0-at2332 c4) ▸
       at 0 2 (K0⁻ ∷ Sw34 ∷ []) (sym (c₁ (K • iI) (Swap ↑ ↑))) ▸
       at 1 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | Kd0 @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-Kd0-at0110243243 : Complete 4 → ⟪ (Bx1-0423 ∷ K1⁻ ∷ []) ⟫ʷ ≈ ⟪ (K1⁻ ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-Kd0-at0110243243 c4 = run b0
  where
  b0 : Chain (Bx1-0423 ∷ K1⁻ ∷ []) (K1⁻ ∷ Bx1-0423 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ c4) ▸
       at 2 2 (K0⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ K1⁻ ∷ []) (K0⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (K0⁻ ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-Kd0-at243243 c4) ▸
       at 0 2 (K1⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ K0⁻ ∷ []) (K1⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | Kd0 @0210243143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-Kd0-at0210243143 : Complete 4 → ⟪ (Bx2-0413 ∷ K2⁻ ∷ []) ⟫ʷ ≈ ⟪ (K2⁻ ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-Kd0-at0210243143 c4 = run b0
  where
  b0 : Chain (Bx2-0413 ∷ K2⁻ ∷ []) (K2⁻ ∷ Bx2-0413 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ c4) ▸
       at 2 2 (K1⁻ ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ K2⁻ ∷ []) (K1⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (K1⁻ ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-Kd0-at0110243243 c4) ▸
       at 0 2 (K2⁻ ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ K1⁻ ∷ []) (K2⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CSd04 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd04-at2332 : Complete 4 → ⟪ (Bx0-1324 ∷ CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS04⁻ ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd04-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ c4) ▸
       at 2 2 (CS04⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd04 c4) ▸
       at 1 2 (CS04⁻ ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd04 c4) ▸
       at 0 2 (CS04⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd04 c4) ▸
       at 1 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CSd04 @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd04-at243243 : Complete 4 → ⟪ (Bx0-1423 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd04-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Bx0-1423 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ c4) ▸
       at 2 2 (CS04⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd03 c4) ▸
       at 1 2 (CS04⁻ ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd04-at2332 c4) ▸
       at 0 2 (CS03⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd04 c4) ▸
       at 1 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CSd04 @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd04-at0110243243 : Complete 4 → ⟪ (Bx1-0423 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd04-at0110243243 c4 = run b0
  where
  b0 : Chain (Bx1-0423 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ Bx1-0423 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ c4) ▸
       at 2 2 (CS03⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS13⁻ ∷ []) (CS03⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS03⁻ ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd04-at243243 c4) ▸
       at 0 2 (CS13⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS03⁻ ∷ []) (CS13⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CSd04 @0210243143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd04-at0210243143 : Complete 4 → ⟪ (Bx2-0413 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd04-at0210243143 c4 = run b0
  where
  b0 : Chain (Bx2-0413 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Bx2-0413 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ c4) ▸
       at 2 2 (CS13⁻ ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS23⁻ ∷ []) (CS13⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS13⁻ ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd04-at0110243243 c4) ▸
       at 0 2 (CS23⁻ ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS13⁻ ∷ []) (CS23⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOX(3;1;4;0) @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨3·1·4·0⟩-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ Sb2-1-4-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-4-0 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨3·1·4·0⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ Sb2-1-4-0 ∷ []) (Sb2-1-4-0 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (Sb3-1-4-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·1·4·0⟩ c4) ▸
       at 1 2 (Sb3-1-4-0 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨3·1·4·0⟩ c4) ▸
       at 0 2 (Sb2-1-4-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·1·4·0⟩ c4) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOX(3;1;4;0) @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨3·1·4·0⟩-at243243 : Complete 4 → ⟪ (Sb0-1-42-3 ∷ Sb2-1-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-3-0 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨3·1·4·0⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ Sb2-1-3-0 ∷ []) (Sb2-1-3-0 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ c4) ▸
       at 2 2 (Sb2-1-4-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·1·3·0⟩ c4) ▸
       at 1 2 (Sb2-1-4-0 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨3·1·4·0⟩-at2332 c4) ▸
       at 0 2 (Sb2-1-3-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·1·4·0⟩ c4) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


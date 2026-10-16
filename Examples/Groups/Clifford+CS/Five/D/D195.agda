{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D195 where

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
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-beta-T-at243243 ; lem-sym23 ; lem-sym34)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-sym12-at132132 ; lem-sym23-at132132)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-sym23-at2332 ; lem-sym34-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-sym12-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-CSd12-beta-at2332 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ324-at2332 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CS23-at2332 ; lem-beta-T-at0310243142)
open import Examples.Groups.Clifford+CS.Five.D.D007 using (lem-SBsym-at0113203442 ; lem-T312-beta-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D013 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D080 using (lem-sym23-at1331)
open import Examples.Groups.Clifford+CS.Five.D.D135 using (lem-F0-at0112203443 ; lem-sym12-at04103143 ; lem-sym12-at04233240)
open import Examples.Groups.Clifford+CS.Five.D.D136 using (lem-CX23-beta-at0413203142 ; lem-CX23-beta-at122331 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at04233240 ; lem-sym12-at0412203143 ; lem-sym12-at0413213240 ; lem-sym12-at122331 ; lem-sym12-at1331 ; lem-sym23-at0412203143 ; lem-sym23-at0413203142 ; lem-sym23-at0413213042 ; lem-sym34-at0413213042 ; lem-sym34-at0413213240)
open import Examples.Groups.Clifford+CS.Five.D.D137 using (lem-auto-BOX⟨0·1234⟩-∣-CCZ403 ; lem-auto-CS01-∣-BOX⟨1·2304⟩ ; lem-auto-CSd01-∣-BOX⟨1·2304⟩ ; lem-beta-T-at0412203143)
open import Examples.Groups.Clifford+CS.Five.D.D138 using (lem-auto-BOX⟨0·1234⟩-∣-CCZ123)
open import Examples.Groups.Clifford+CS.Five.D.D152 using (lem-CX23-beta-at042042 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ143-at04233240 ; lem-sym23-at042042 ; lem-sym23-at04233042 ; lem-sym34-at04233042 ; lem-sym34-at04233240)
open import Examples.Groups.Clifford+CS.Five.D.D160 using (lem-auto-BOX⟨0·1234⟩-∣-CSd23 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CS03-at2332 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CS13-at2332 ; lem-beta-T-at03243042)
open import Examples.Groups.Clifford+CS.Five.D.D183 using (lem-auto-CCZ012-∣-CCZ342-at0410233142)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-CCZ023 ; lem-nat-2-BOX⟨0·1234⟩ ; lem-nat-2-BOX⟨0·1324⟩)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-0-CCZ134)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-0-TOFF402)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-0-BOX⟨0·1234⟩ ; lem-nat-0-BOX⟨1·0234⟩ ; lem-nat-1-BOX⟨1·0234⟩ ; lem-nat-1-BOX⟨2·0134⟩ ; lem-nat-2-BOX⟨2·0134⟩ ; lem-nat-2-BOX⟨2·0413⟩ ; lem-nat-2-BOX⟨3·0124⟩ ; lem-nat-2-BOX⟨3·0412⟩)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-nat-1-CS01 ; lem-nat-1-CS02)
open import Examples.Groups.Clifford+CS.Five.D.R013 using (lem-nat-2-CSd12 ; lem-nat-2-CSd13)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-0-BOX⟨2·0413⟩ ; lem-nat-0-BOX⟨2·1403⟩ ; lem-nat-1-CSd02 ; lem-nat-2-CSd02)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-1-CSd01)
open import Examples.Groups.Clifford+CS.Five.D.R016 using (lem-nat-1-BOX⟨4·0312⟩)
open import Examples.Groups.Clifford+CS.Five.D.R017 using (lem-nat-3-BOX⟨3·0124⟩ ; lem-nat-3-BOX⟨4·0123⟩)
open import Examples.Groups.Clifford+CS.Five.D.R019 using (lem-nat-2-CSd03 ; lem-nat-2-SBOXd⟨0·1·2·3⟩ ; lem-nat-2-SBOXd⟨0·1·3·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R023 using (lem-nat-3-BOX⟨1·2304⟩ ; lem-nat-3-BOX⟨1·2403⟩)
open import Examples.Groups.Clifford+CS.Five.D.R024 using (lem-nat-1-BOX⟨1·2403⟩ ; lem-nat-1-BOX⟨2·1403⟩)
open import Examples.Groups.Clifford+CS.Five.D.R029 using (lem-comm-SBOXd⟨0·1·2·3⟩-TOFF304 ; lem-nat-0-BOX⟨4·0321⟩ ; lem-nat-0-BOX⟨4·1320⟩ ; lem-nat-1-BOX⟨4·0213⟩ ; lem-nat-1-BOX⟨4·0321⟩ ; lem-nat-2-BOX⟨4·0312⟩)
open import Examples.Groups.Clifford+CS.Five.D.R030 using (lem-comm-SBOXd⟨0·1·2·3⟩-TOFF403 ; lem-nat-1-BOX⟨4·0123⟩ ; lem-nat-2-BOX⟨4·0213⟩)
open import Examples.Groups.Clifford+CS.Five.D.R033 using (lem-nat-1-BOX⟨3·2401⟩)
open import Examples.Groups.Clifford+CS.Five.D.R040 using (lem-nat-0-BOX⟨3·2410⟩)
open import Examples.Groups.Clifford+CS.Five.D.R041 using (lem-nat-0-BOX⟨4·2103⟩)
-- F4 CS12^0|K3^1: 131 steps
lem-F4-CS12ᵖ0∣K3ᵖ1 : Complete 4 → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS12ᵖ0∣K3ᵖ1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (run b16))))))))))))))))
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK43 ∷ []) (ι ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ [])
  b0 = at 3 1 (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ []) (lw1 c4 (CK43 ∷ []) (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (ι ∷ X4 ∷ []) (zc) ▸
       at 1 2 (ι ∷ Sb0-1-42-3 ∷ []) (zc) ▸
       at 0 2 (ι ∷ X4 ∷ []) (zc) ▸
       at 2 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (ι ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ []) (ι ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ S4⁻ ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ [])
  b1 = at 12 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 1 (CS13⁻ ∷ []) (refl) ▸
       at 13 4 (S4⁻ ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS13⁻ ∷ X4 ∷ S4⁻ ∷ []) (S4⁻ ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 10 4 (S4⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff324 ∷ X4 ∷ S4⁻ ∷ []) (S4⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 1 (CS13 ∷ []) (refl) ▸
       at 7 4 (S4⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS13 ∷ X4 ∷ S4⁻ ∷ []) (S4⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 1 (Sb0-1-3-2 ∷ []) (refl) ▸ done

  b2 : Chain (ι ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ S4⁻ ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ []) (ι ∷ X4 ∷ Toff014 ∷ X4 ∷ S4⁻ ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ [])
  b2 = at 4 4 (S4⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff324 ∷ X4 ∷ S4⁻ ∷ []) (S4⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at243243 c4) ▸
       at 3 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 4 (S4⁻ ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CCZ023 ∷ X4 ∷ S4⁻ ∷ []) (S4⁻ ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 4 (S4⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff014 ∷ X4 ∷ S4⁻ ∷ []) (S4⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 4 (S4⁻ ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CCZ023 ∷ X4 ∷ S4⁻ ∷ []) (S4⁻ ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b3 : Chain (ι ∷ X4 ∷ Toff014 ∷ X4 ∷ S4⁻ ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ [])
  b3 = at 1 4 (S4⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff014 ∷ X4 ∷ S4⁻ ∷ []) (S4⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 3 4 (Bx0-1423 ∷ []) (sym (lem-beta-T-at243243 c4)) ▸
       at 4 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b4 : Chain (ι ∷ S4⁻ ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ [])
  b4 = at 7 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 3 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 1 (CS13⁻ ∷ []) (refl) ▸ done

  b5 : Chain (ι ∷ S4⁻ ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ X4 ∷ CS34 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ [])
  b5 = at 14 4 (CS34 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS13⁻ ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 11 4 (CS34 ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff324 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ Toff324 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 1 (CS13 ∷ []) (refl) ▸
       at 8 4 (CS34 ∷ X4 ∷ CS13 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS13 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS13 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 5 4 (CS34 ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff324 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ Toff324 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at243243 c4) ▸ done

  b6 : Chain (ι ∷ S4⁻ ∷ X4 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ X4 ∷ CS34 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ []) (ι ∷ S4⁻ ∷ CS34 ∷ X4 ∷ Toff014 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ [])
  b6 = at 4 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 4 (CS34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CCZ023 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 4 (CS34 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff014 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 4 (CS34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CCZ023 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (CS34 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff014 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b7 : Chain (ι ∷ S4⁻ ∷ CS34 ∷ X4 ∷ Toff014 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ []) (ι ∷ S4⁻ ∷ CS34 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ [])
  b7 = at 6 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 4 4 (Bx0-1423 ∷ []) (sym (lem-beta-T-at243243 c4)) ▸
       at 5 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 4 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done

  b8 : Chain (ι ∷ S4⁻ ∷ CS34 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ []) (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS34 ∷ K3 ∷ CS34 ∷ [])
  b8 = at 5 2 (K3 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ K3 ∷ []) (K3 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (K3 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at243243 c4) ▸
       at 3 2 (K3 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ K3 ∷ []) (K3 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b9 : Chain (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS34 ∷ K3 ∷ CS34 ∷ []) (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ CS34 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K3 ∷ CS34 ∷ [])
  b9 = at 17 1 (CS13⁻ ∷ []) (refl) ▸
       at 16 4 (CS34 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS13⁻ ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 18 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 13 4 (CS34 ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff324 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ Toff324 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 1 (CS13 ∷ []) (refl) ▸
       at 10 4 (CS34 ∷ X4 ∷ CS13 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS13 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS13 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 7 4 (CS34 ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff324 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ Toff324 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b10 : Chain (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ CS34 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K3 ∷ CS34 ∷ []) (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K3 ∷ CS34 ∷ [])
  b10 = at 5 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at243243 c4) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 4 (CS34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CCZ023 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 4 (CS34 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff014 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 4 (CS34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CCZ023 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 4 (CS34 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff014 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b11 : Chain (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K3 ∷ CS34 ∷ []) (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K3 ∷ CS34 ∷ [])
  b11 = at 7 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 9 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 6 4 (Bx0-1423 ∷ []) (sym (lem-beta-T-at243243 c4)) ▸
       at 7 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 9 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 10 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b12 : Chain (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K3 ∷ CS34 ∷ []) (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS34 ∷ [])
  b12 = at 6 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 7 2 (K3 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ K3 ∷ []) (K3 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (K3 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at243243 c4) ▸
       at 5 2 (K3 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ K3 ∷ []) (K3 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b13 : Chain (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS34 ∷ []) (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ [])
  b13 = at 17 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 1 (CS13⁻ ∷ []) (refl) ▸
       at 18 4 (CS34 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS13⁻ ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 20 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 15 4 (CS34 ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff324 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ Toff324 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 1 (CS13 ∷ []) (refl) ▸
       at 12 4 (CS34 ∷ X4 ∷ CS13 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS13 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS13 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 1 (Sb0-1-3-2 ∷ []) (refl) ▸ done

  b14 : Chain (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ []) (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ X4 ∷ Toff014 ∷ X4 ∷ CS34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ [])
  b14 = at 9 4 (CS34 ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff324 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ Toff324 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at243243 c4) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 4 (CS34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CCZ023 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 4 (CS34 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff014 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 4 (CS34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CCZ023 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b15 : Chain (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ X4 ∷ Toff014 ∷ X4 ∷ CS34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ []) (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ [])
  b15 = at 6 4 (CS34 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff014 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 10 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 11 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 8 4 (Bx0-1423 ∷ []) (sym (lem-beta-T-at243243 c4)) ▸
       at 9 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 10 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 11 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b16 : Chain (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ []) (CK43 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b16 = at 12 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 8 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 0 7 (CK43 ∷ []) (lw1 c4 (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ []) (CK43 ∷ []) tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;2;3) | TOFF403: 1 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-TOFF403 : Complete 4 → ⟪ (Sb⁻0-1-2-3 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ Sb⁻0-1-2-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-TOFF403 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-2-3 ∷ Toff403 ∷ []) (Toff403 ∷ Sb⁻0-1-2-3 ∷ [])
  b0 = at 0 2 (Toff403 ∷ Sb⁻0-1-2-3 ∷ []) (lem-comm-SBOXd⟨0·1·2·3⟩-TOFF403 c4) ▸ done


-- auto BOX(0;1234) | CSd23 @0110: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd23-at0110 : Complete 4 → ⟪ (Bx1-0234 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ Bx1-0234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd23-at0110 c4 = run b0
  where
  b0 : Chain (Bx1-0234 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Bx1-0234 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0234⟩ c4) ▸
       at 2 2 (CS23⁻ ∷ Sw01 ∷ []) (c₂ (Swap) (CS • CS • CS)) ▸
       at 1 2 (CS23⁻ ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd23 c4) ▸
       at 0 2 (CS23⁻ ∷ Sw01 ∷ []) (c₂ (Swap) (CS • CS • CS)) ▸
       at 1 2 (Bx1-0234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CSd23 @021021: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd23-at021021 : Complete 4 → ⟪ (Bx2-0134 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ Bx2-0134 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd23-at021021 c4 = run b0
  where
  b0 : Chain (Bx2-0134 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ Bx2-0134 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0134⟩ c4) ▸
       at 2 2 (CS23⁻ ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS13⁻ ∷ []) (CS23⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS23⁻ ∷ Bx1-0234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd23-at0110 c4) ▸
       at 0 2 (CS13⁻ ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS23⁻ ∷ []) (CS13⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-0134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CSd23 @03102132: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd23-at03102132 : Complete 4 → ⟪ (Bx3-0124 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ Bx3-0124 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd23-at03102132 c4 = run b0
  where
  b0 : Chain (Bx3-0124 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ Bx3-0124 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-0134 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0124⟩ c4) ▸
       at 2 2 (CS13⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd12 c4) ▸
       at 1 2 (CS13⁻ ∷ Bx2-0134 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd23-at021021 c4) ▸
       at 0 2 (CS12⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd13 c4) ▸
       at 1 2 (Bx3-0124 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0134⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CSd23 @0410213243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd23-at0410213243 : Complete 4 → ⟪ (Bx4-0123 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ Bx4-0123 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd23-at0410213243 c4 = run b0
  where
  b0 : Chain (Bx4-0123 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ Bx4-0123 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-0124 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·0123⟩ c4) ▸
       at 2 2 (CS12⁻ ∷ Sw34 ∷ []) (sym (c₃ ((CS • CS • CS) ↑) (Swap))) ▸
       at 1 2 (CS12⁻ ∷ Bx3-0124 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd23-at03102132 c4) ▸
       at 0 2 (CS12⁻ ∷ Sw34 ∷ []) (sym (c₃ ((CS • CS • CS) ↑) (Swap))) ▸
       at 1 2 (Bx4-0123 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·0124⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CSd23 @04103143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd23-at04103143 : Complete 4 → ⟪ (Bx4-0213 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ Bx4-0213 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd23-at04103143 c4 = run b0
  where
  b0 : Chain (Bx4-0213 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ Bx4-0213 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-0123 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0213⟩ c4) ▸
       at 2 2 (CS12⁻ ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS12⁻ ∷ Bx4-0123 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd23-at0410213243 c4) ▸
       at 0 2 (CS12⁻ ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-0213 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0123⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CSd23 @0410233142: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd23-at0410233142 : Complete 4 → ⟪ (Bx4-0312 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ Bx4-0312 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd23-at0410233142 c4 = run b0
  where
  b0 : Chain (Bx4-0312 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ Bx4-0312 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-0213 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0312⟩ c4) ▸
       at 2 2 (CS12⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd13 c4) ▸
       at 1 2 (CS12⁻ ∷ Bx4-0213 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd23-at04103143 c4) ▸
       at 0 2 (CS13⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd12 c4) ▸
       at 1 2 (Bx4-0312 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0213⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CSd23 @0410233241: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd23-at0410233241 : Complete 4 → ⟪ (Bx4-0321 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ Bx4-0321 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd23-at0410233241 c4 = run b0
  where
  b0 : Chain (Bx4-0321 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Bx4-0321 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-0312 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0321⟩ c4) ▸
       at 2 2 (CS13⁻ ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS23⁻ ∷ []) (CS13⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS13⁻ ∷ Bx4-0312 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd23-at0410233142 c4) ▸
       at 0 2 (CS23⁻ ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS13⁻ ∷ []) (CS23⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-0321 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0312⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CSd23 @04233240: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd23-at04233240 : Complete 4 → ⟪ (Bx4-1320 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ Bx4-1320 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd23-at04233240 c4 = run b0
  where
  b0 : Chain (Bx4-1320 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Bx4-1320 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-0321 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·1320⟩ c4) ▸
       at 2 2 (CS23⁻ ∷ Sw01 ∷ []) (c₂ (Swap) (CS • CS • CS)) ▸
       at 1 2 (CS23⁻ ∷ Bx4-0321 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd23-at0410233241 c4) ▸
       at 0 2 (CS23⁻ ∷ Sw01 ∷ []) (c₂ (Swap) (CS • CS • CS)) ▸
       at 1 2 (Bx4-1320 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·0321⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CCZ203: 34 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ203 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ203 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (run b4))))
  where
  b0 : Chain (Sb0-1-23-4 ∷ CCZ023 ∷ []) (CS23 ∷ Bx4-1320 ∷ Toff023 ∷ Sb4-1-0-2 ∷ Toff023 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ Sb⁻4-1-0-2 ∷ CS02 ∷ [])
  b0 = at 1 1 (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) (lw4 c4 (CCZ023 ∷ []) (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS23 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS23-at2332 c4) ▸
       at 1 1 (Sb4-1-32-0 ∷ []) (lem-F0-at0112203443 c4) ▸
       at 1 1 (Bx4-1320 ∷ Toff023 ∷ Sb4-1-0-2 ∷ Toff023 ∷ Sb⁻4-1-0-2 ∷ []) (refl) ▸
       at 5 1 (CS01⁻ ∷ []) (refl) ▸
       at 5 4 (CX03 ∷ CS23⁻ ∷ CX03 ∷ CS01⁻ ∷ []) (lw4 c4 (CS01⁻ ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ []) (CX03 ∷ CS23⁻ ∷ CX03 ∷ CS01⁻ ∷ []) tt tt Eq.refl) ▸
       at 8 1 (Sb⁻4-1-0-2 ∷ []) (refl) ▸ done

  b1 : Chain (CS23 ∷ Bx4-1320 ∷ Toff023 ∷ Sb4-1-0-2 ∷ Toff023 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ Sb⁻4-1-0-2 ∷ CS02 ∷ []) (CS23 ∷ CX03 ∷ Bx4-1302 ∷ CCZ012 ∷ CS23⁻ ∷ CX03 ∷ Toff023 ∷ Sb4-1-0-2 ∷ Toff023 ∷ Sb⁻4-1-0-2 ∷ CS02 ∷ [])
  b1 = at 3 1 (CS01 ∷ []) (refl) ▸
       at 2 6 (CX03 ∷ CS23⁻ ∷ CX03 ∷ Toff023 ∷ CS01 ∷ Toff023 ∷ []) (lw4 c4 (Toff023 ∷ CS01 ∷ Toff023 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ []) (CX03 ∷ CS23⁻ ∷ CX03 ∷ Toff023 ∷ CS01 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sb4-1-0-2 ∷ []) (refl) ▸
       at 1 0 (CX03 ∷ CX03 ∷ []) (lw4 c4 [] (CX03 ∷ CX03 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Bx4-1302 ∷ []) (lem-sym34-at04233240 c4) ▸
       at 3 1 (Bx4-1032 ∷ []) (lem-sym23-at04233042 c4) ▸
       at 2 3 (Bx4-1032 ∷ CCZ012 ∷ []) (lem-CX23-beta-at042042 c4) ▸
       at 2 1 (Bx4-1302 ∷ []) (lem-sym23-at042042 c4) ▸ done

  b2 : Chain (CS23 ∷ CX03 ∷ Bx4-1302 ∷ CCZ012 ∷ CS23⁻ ∷ CX03 ∷ Toff023 ∷ Sb4-1-0-2 ∷ Toff023 ∷ Sb⁻4-1-0-2 ∷ CS02 ∷ []) (CS23 ∷ CX03 ∷ CCZ012 ∷ CS23⁻ ∷ CX03 ∷ Bx4-1302 ∷ CCZ012 ∷ Toff023 ∷ Sb4-1-0-2 ∷ Toff023 ∷ Sb⁻4-1-0-2 ∷ CS02 ∷ [])
  b2 = at 2 1 (Bx4-1320 ∷ []) (lem-sym34-at04233042 c4) ▸
       at 2 2 (CCZ012 ∷ Bx4-1320 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ143-at04233240 c4) ▸
       at 3 2 (CS23⁻ ∷ Bx4-1320 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd23-at04233240 c4) ▸
       at 4 0 (CX03 ∷ CX03 ∷ []) (lw4 c4 [] (CX03 ∷ CX03 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Bx4-1302 ∷ []) (lem-sym34-at04233240 c4) ▸
       at 6 1 (Bx4-1032 ∷ []) (lem-sym23-at04233042 c4) ▸
       at 5 3 (Bx4-1032 ∷ CCZ012 ∷ []) (lem-CX23-beta-at042042 c4) ▸
       at 5 1 (Bx4-1302 ∷ []) (lem-sym23-at042042 c4) ▸ done

  b3 : Chain (CS23 ∷ CX03 ∷ CCZ012 ∷ CS23⁻ ∷ CX03 ∷ Bx4-1302 ∷ CCZ012 ∷ Toff023 ∷ Sb4-1-0-2 ∷ Toff023 ∷ Sb⁻4-1-0-2 ∷ CS02 ∷ []) (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ Sb0-1-32-4 ∷ [])
  b3 = at 5 1 (Bx4-1320 ∷ []) (lem-sym34-at04233042 c4) ▸
       at 5 2 (CCZ012 ∷ Bx4-1320 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ143-at04233240 c4) ▸
       at 1 2 (CCZ012 ∷ CX03 ∷ []) (lw4 c4 (CX03 ∷ CCZ012 ∷ []) (CCZ012 ∷ CX03 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (CCZ012 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ []) (lw4 c4 (CX03 ∷ CS23⁻ ∷ CX03 ∷ CCZ012 ∷ []) (CCZ012 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ []) tt tt Eq.refl) ▸
       at 1 2 [] (lw4 c4 (CCZ012 ∷ CCZ012 ∷ []) [] tt tt Eq.refl) ▸
       at 4 5 (Sb4-1-32-0 ∷ []) (refl) ▸
       at 4 1 (Sb0-1-32-4 ∷ []) (sym (lem-F0-at0112203443 c4)) ▸
       at 4 2 (CS02 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS03-at2332 c4) ▸ done

  b4 : Chain (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ Sb0-1-32-4 ∷ []) (CCZ023 ∷ Sb0-1-23-4 ∷ [])
  b4 = at 5 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 5 (CCZ023 ∷ []) (lw4 c4 (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CSd13: 3 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd13 : Complete 4 → ⟪ (Bx0-1234 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd13 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ Bx0-1234 ∷ [])
  b0 = at 0 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 0 2 (CS13⁻ ∷ Bx0-1324 ∷ []) (sym (lem-CSd12-beta-at2332 c4)) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸ done


-- auto BOX(0;1234) | CSd13 @0110: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd13-at0110 : Complete 4 → ⟪ (Bx1-0234 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ Bx1-0234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd13-at0110 c4 = run b0
  where
  b0 : Chain (Bx1-0234 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Bx1-0234 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0234⟩ c4) ▸
       at 2 2 (CS13⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS03⁻ ∷ []) (CS13⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS13⁻ ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd13 c4) ▸
       at 0 2 (CS03⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS13⁻ ∷ []) (CS03⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CSd13 @021021: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd13-at021021 : Complete 4 → ⟪ (Bx2-0134 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ Bx2-0134 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd13-at021021 c4 = run b0
  where
  b0 : Chain (Bx2-0134 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Bx2-0134 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0134⟩ c4) ▸
       at 2 2 (CS03⁻ ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS03⁻ ∷ Bx1-0234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd13-at0110 c4) ▸
       at 0 2 (CS03⁻ ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-0134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CSd13 @03102132: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd13-at03102132 : Complete 4 → ⟪ (Bx3-0124 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ Bx3-0124 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd13-at03102132 c4 = run b0
  where
  b0 : Chain (Bx3-0124 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ Bx3-0124 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-0134 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0124⟩ c4) ▸
       at 2 2 (CS03⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd02 c4) ▸
       at 1 2 (CS03⁻ ∷ Bx2-0134 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd13-at021021 c4) ▸
       at 0 2 (CS02⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd03 c4) ▸
       at 1 2 (Bx3-0124 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0134⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CSd13 @0410213243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd13-at0410213243 : Complete 4 → ⟪ (Bx4-0123 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ Bx4-0123 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd13-at0410213243 c4 = run b0
  where
  b0 : Chain (Bx4-0123 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ Bx4-0123 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-0124 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·0123⟩ c4) ▸
       at 2 2 (CS02⁻ ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (Swap))) ▸
       at 1 2 (CS02⁻ ∷ Bx3-0124 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd13-at03102132 c4) ▸
       at 0 2 (CS02⁻ ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (Swap))) ▸
       at 1 2 (Bx4-0123 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·0124⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CSd13 @04103143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd13-at04103143 : Complete 4 → ⟪ (Bx4-0213 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ Bx4-0213 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd13-at04103143 c4 = run b0
  where
  b0 : Chain (Bx4-0213 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ Bx4-0213 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-0123 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0213⟩ c4) ▸
       at 2 2 (CS02⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd01 c4) ▸
       at 1 2 (CS02⁻ ∷ Bx4-0123 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd13-at0410213243 c4) ▸
       at 0 2 (CS01⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd02 c4) ▸
       at 1 2 (Bx4-0213 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0123⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CSd13 @0410233142: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd13-at0410233142 : Complete 4 → ⟪ (Bx4-0312 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ Bx4-0312 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd13-at0410233142 c4 = run b0
  where
  b0 : Chain (Bx4-0312 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ Bx4-0312 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-0213 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0312⟩ c4) ▸
       at 2 2 (CS01⁻ ∷ Sw23 ∷ []) (sym (c₂ (CS • CS • CS) (Swap))) ▸
       at 1 2 (CS01⁻ ∷ Bx4-0213 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd13-at04103143 c4) ▸
       at 0 2 (CS01⁻ ∷ Sw23 ∷ []) (sym (c₂ (CS • CS • CS) (Swap))) ▸
       at 1 2 (Bx4-0312 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0213⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CSd13 @0410233241: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd13-at0410233241 : Complete 4 → ⟪ (Bx4-0321 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ Bx4-0321 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd13-at0410233241 c4 = run b0
  where
  b0 : Chain (Bx4-0321 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ Bx4-0321 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-0312 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0321⟩ c4) ▸
       at 2 2 (CS01⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd02 c4) ▸
       at 1 2 (CS01⁻ ∷ Bx4-0312 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd13-at0410233142 c4) ▸
       at 0 2 (CS02⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd01 c4) ▸
       at 1 2 (Bx4-0321 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0312⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CSd13 @04233240: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd13-at04233240 : Complete 4 → ⟪ (Bx4-1320 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ Bx4-1320 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd13-at04233240 c4 = run b0
  where
  b0 : Chain (Bx4-1320 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ Bx4-1320 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-0321 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·1320⟩ c4) ▸
       at 2 2 (CS02⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS12⁻ ∷ []) (CS02⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS02⁻ ∷ Bx4-0321 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd13-at0410233241 c4) ▸
       at 0 2 (CS12⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS02⁻ ∷ []) (CS12⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-1320 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·0321⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CCZ201: 38 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ201 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ201 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (run b4))))
  where
  b0 : Chain (Sb0-1-23-4 ∷ CCZ012 ∷ []) (CS12 ∷ Bx4-1320 ∷ Toff023 ∷ Sb4-1-0-2 ∷ Toff023 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sb⁻4-1-0-2 ∷ CS02 ∷ [])
  b0 = at 1 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS12 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS13-at2332 c4) ▸
       at 1 1 (Sb4-1-32-0 ∷ []) (lem-F0-at0112203443 c4) ▸
       at 1 1 (Bx4-1320 ∷ Toff023 ∷ Sb4-1-0-2 ∷ Toff023 ∷ Sb⁻4-1-0-2 ∷ []) (refl) ▸
       at 5 1 (CS01⁻ ∷ []) (refl) ▸
       at 5 4 (CX01 ∷ CS12⁻ ∷ CX01 ∷ CS01⁻ ∷ []) (lw4 c4 (CS01⁻ ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ []) (CX01 ∷ CS12⁻ ∷ CX01 ∷ CS01⁻ ∷ []) tt tt Eq.refl) ▸
       at 8 1 (Sb⁻4-1-0-2 ∷ []) (refl) ▸ done

  b1 : Chain (CS12 ∷ Bx4-1320 ∷ Toff023 ∷ Sb4-1-0-2 ∷ Toff023 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sb⁻4-1-0-2 ∷ CS02 ∷ []) (CS12 ∷ CX01 ∷ Bx4-3012 ∷ CCZ023 ∷ CS12⁻ ∷ CX01 ∷ Toff023 ∷ Sb4-1-0-2 ∷ Toff023 ∷ Sb⁻4-1-0-2 ∷ CS02 ∷ [])
  b1 = at 3 1 (CS01 ∷ []) (refl) ▸
       at 2 6 (CX01 ∷ CS12⁻ ∷ CX01 ∷ Toff023 ∷ CS01 ∷ Toff023 ∷ []) (lw4 c4 (Toff023 ∷ CS01 ∷ Toff023 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ []) (CX01 ∷ CS12⁻ ∷ CX01 ∷ Toff023 ∷ CS01 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sb4-1-0-2 ∷ []) (refl) ▸
       at 1 0 (CX01 ∷ CX01 ∷ []) (lw4 c4 [] (CX01 ∷ CX01 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Bx4-3120 ∷ []) (lem-sym12-at04233240 c4) ▸
       at 3 1 (Bx4-3102 ∷ []) (lem-sym34-at0413213240 c4) ▸
       at 3 1 (Bx4-3012 ∷ []) (lem-sym23-at0413213042 c4) ▸
       at 2 3 (Bx4-3012 ∷ CCZ023 ∷ []) (lem-CX23-beta-at0413203142 c4) ▸ done

  b2 : Chain (CS12 ∷ CX01 ∷ Bx4-3012 ∷ CCZ023 ∷ CS12⁻ ∷ CX01 ∷ Toff023 ∷ Sb4-1-0-2 ∷ Toff023 ∷ Sb⁻4-1-0-2 ∷ CS02 ∷ []) (CS12 ∷ CX01 ∷ CCZ023 ∷ CS12⁻ ∷ CX01 ∷ CX01 ∷ Bx4-3102 ∷ CX01 ∷ Toff023 ∷ Sb4-1-0-2 ∷ Toff023 ∷ Sb⁻4-1-0-2 ∷ CS02 ∷ [])
  b2 = at 2 1 (Bx4-3102 ∷ []) (lem-sym23-at0413203142 c4) ▸
       at 2 1 (Bx4-3120 ∷ []) (lem-sym34-at0413213042 c4) ▸
       at 2 1 (Bx4-1320 ∷ []) (lem-sym12-at0413213240 c4) ▸
       at 2 2 (CCZ023 ∷ Bx4-1320 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at04233240 c4) ▸
       at 3 2 (CS12⁻ ∷ Bx4-1320 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd13-at04233240 c4) ▸
       at 4 0 (CX01 ∷ CX01 ∷ []) (lw4 c4 [] (CX01 ∷ CX01 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Bx4-3120 ∷ []) (lem-sym12-at04233240 c4) ▸
       at 6 1 (Bx4-3102 ∷ []) (lem-sym34-at0413213240 c4) ▸ done

  b3 : Chain (CS12 ∷ CX01 ∷ CCZ023 ∷ CS12⁻ ∷ CX01 ∷ CX01 ∷ Bx4-3102 ∷ CX01 ∷ Toff023 ∷ Sb4-1-0-2 ∷ Toff023 ∷ Sb⁻4-1-0-2 ∷ CS02 ∷ []) (CS12 ∷ CCZ023 ∷ CCZ023 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Bx4-1320 ∷ Toff023 ∷ Sb4-1-0-2 ∷ Toff023 ∷ Sb⁻4-1-0-2 ∷ CS02 ∷ [])
  b3 = at 6 1 (Bx4-3012 ∷ []) (lem-sym23-at0413213042 c4) ▸
       at 5 3 (Bx4-3012 ∷ CCZ023 ∷ []) (lem-CX23-beta-at0413203142 c4) ▸
       at 5 1 (Bx4-3102 ∷ []) (lem-sym23-at0413203142 c4) ▸
       at 5 1 (Bx4-3120 ∷ []) (lem-sym34-at0413213042 c4) ▸
       at 5 1 (Bx4-1320 ∷ []) (lem-sym12-at0413213240 c4) ▸
       at 5 2 (CCZ023 ∷ Bx4-1320 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at04233240 c4) ▸
       at 1 2 (CCZ023 ∷ CX01 ∷ []) (lw4 c4 (CX01 ∷ CCZ023 ∷ []) (CCZ023 ∷ CX01 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (CCZ023 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ []) (lw4 c4 (CX01 ∷ CS12⁻ ∷ CX01 ∷ CCZ023 ∷ []) (CCZ023 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ []) tt tt Eq.refl) ▸ done

  b4 : Chain (CS12 ∷ CCZ023 ∷ CCZ023 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Bx4-1320 ∷ Toff023 ∷ Sb4-1-0-2 ∷ Toff023 ∷ Sb⁻4-1-0-2 ∷ CS02 ∷ []) (CCZ012 ∷ Sb0-1-23-4 ∷ [])
  b4 = at 1 2 [] (lw4 c4 (CCZ023 ∷ CCZ023 ∷ []) [] tt tt Eq.refl) ▸
       at 4 5 (Sb4-1-32-0 ∷ []) (refl) ▸
       at 4 1 (Sb0-1-32-4 ∷ []) (sym (lem-F0-at0112203443 c4)) ▸
       at 4 2 (CS02 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS03-at2332 c4) ▸
       at 5 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 5 (CCZ012 ∷ []) (lw4 c4 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CSd13 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd13-at2332 : Complete 4 → ⟪ (Bx0-1324 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd13-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ c4) ▸
       at 2 2 (CS13⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd12 c4) ▸
       at 1 2 (CS13⁻ ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd13 c4) ▸
       at 0 2 (CS12⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd13 c4) ▸
       at 1 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CCZ231: 38 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ231 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ231 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (run b4))))
  where
  b0 : Chain (Sb0-1-23-4 ∷ CCZ123 ∷ []) (CS12 ∷ Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS23 ∷ [])
  b0 = at 1 1 (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS12 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS13-at2332 c4) ▸
       at 1 1 (Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ []) (refl) ▸
       at 5 1 (CS14⁻ ∷ []) (refl) ▸
       at 5 4 (CX31 ∷ CS12⁻ ∷ CX31 ∷ CS14⁻ ∷ []) (lw0 c4 (CS14⁻ ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ []) (CX31 ∷ CS12⁻ ∷ CX31 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 8 1 (Sb⁻0-1-4-2 ∷ []) (refl) ▸
       at 4 4 (CX31 ∷ CS12⁻ ∷ CX31 ∷ Toff423 ∷ []) (lw0 c4 (Toff423 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ []) (CX31 ∷ CS12⁻ ∷ CX31 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CS12 ∷ Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS23 ∷ []) (CS12 ∷ CX31 ∷ CX31 ∷ Bx0-2314 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS23 ∷ [])
  b1 = at 3 1 (CS14 ∷ []) (refl) ▸
       at 3 4 (CX31 ∷ CS12⁻ ∷ CX31 ∷ CS14 ∷ []) (lw0 c4 (CS14 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ []) (CX31 ∷ CS12⁻ ∷ CX31 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sb0-1-4-2 ∷ []) (refl) ▸
       at 2 4 (CX31 ∷ CS12⁻ ∷ CX31 ∷ Toff423 ∷ []) (lw0 c4 (Toff423 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ []) (CX31 ∷ CS12⁻ ∷ CX31 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 1 0 (CX31 ∷ CX31 ∷ []) (lw4 c4 [] (CX31 ∷ CX31 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Bx0-3124 ∷ []) (lem-sym12-at2332 c4) ▸
       at 3 1 (Bx0-3214 ∷ []) (lem-sym23-at132132 c4) ▸
       at 3 1 (Bx0-2314 ∷ []) (lem-sym12-at1331 c4) ▸ done

  b2 : Chain (CS12 ∷ CX31 ∷ CX31 ∷ Bx0-2314 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS23 ∷ []) (CS12 ∷ CX31 ∷ CCZ234 ∷ CS12⁻ ∷ CX31 ∷ CX31 ∷ Bx0-3124 ∷ CX31 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS23 ∷ [])
  b2 = at 2 3 (Bx0-2314 ∷ CCZ234 ∷ []) (lem-CX23-beta-at122331 c4) ▸
       at 2 1 (Bx0-3214 ∷ []) (lem-sym12-at122331 c4) ▸
       at 2 1 (Bx0-3124 ∷ []) (lem-sym23-at1331 c4) ▸
       at 2 1 (Bx0-1324 ∷ []) (lem-sym12-at132132 c4) ▸
       at 2 2 (CCZ234 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ324-at2332 c4) ▸
       at 3 2 (CS12⁻ ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd13-at2332 c4) ▸
       at 4 0 (CX31 ∷ CX31 ∷ []) (lw4 c4 [] (CX31 ∷ CX31 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Bx0-3124 ∷ []) (lem-sym12-at2332 c4) ▸ done

  b3 : Chain (CS12 ∷ CX31 ∷ CCZ234 ∷ CS12⁻ ∷ CX31 ∷ CX31 ∷ Bx0-3124 ∷ CX31 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS23 ∷ []) (CS12 ∷ CCZ234 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CCZ234 ∷ Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS23 ∷ [])
  b3 = at 6 1 (Bx0-3214 ∷ []) (lem-sym23-at132132 c4) ▸
       at 6 1 (Bx0-2314 ∷ []) (lem-sym12-at1331 c4) ▸
       at 5 3 (Bx0-2314 ∷ CCZ234 ∷ []) (lem-CX23-beta-at122331 c4) ▸
       at 5 1 (Bx0-3214 ∷ []) (lem-sym12-at122331 c4) ▸
       at 5 1 (Bx0-3124 ∷ []) (lem-sym23-at1331 c4) ▸
       at 5 1 (Bx0-1324 ∷ []) (lem-sym12-at132132 c4) ▸
       at 5 2 (CCZ234 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ324-at2332 c4) ▸
       at 1 2 (CCZ234 ∷ CX31 ∷ []) (lw0 c4 (CX31 ∷ CCZ234 ∷ []) (CCZ234 ∷ CX31 ∷ []) tt tt Eq.refl) ▸ done

  b4 : Chain (CS12 ∷ CCZ234 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CCZ234 ∷ Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS23 ∷ []) (CCZ123 ∷ Sb0-1-23-4 ∷ [])
  b4 = at 2 4 (CCZ234 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ []) (lw0 c4 (CX31 ∷ CS12⁻ ∷ CX31 ∷ CCZ234 ∷ []) (CCZ234 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ []) tt tt Eq.refl) ▸
       at 1 2 [] (lw0 c4 (CCZ234 ∷ CCZ234 ∷ []) [] tt tt Eq.refl) ▸
       at 4 5 (Sb0-1-32-4 ∷ []) (refl) ▸
       at 4 2 (CS23 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS23-at2332 c4) ▸
       at 5 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 5 (CCZ123 ∷ []) (lw4 c4 (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(3;0412): 10 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨3·0412⟩ : Complete 4 → ⟪ (Sb⁻0-1-2-3 ∷ Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ Sb⁻0-1-2-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨3·0412⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb⁻0-1-2-3 ∷ Bx3-0412 ∷ []) (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ CS12⁻ ∷ [])
  b0 = at 1 1 (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-beta-T-at0310243142 c4) ▸
       at 0 2 (Toff304 ∷ Sb⁻0-1-2-3 ∷ []) (lem-comm-SBOXd⟨0·1·2·3⟩-TOFF304 c4) ▸
       at 1 1 (CS12⁻ ∷ []) (refl) ▸
       at 1 2 (CCZ123 ∷ CS12⁻ ∷ []) (lw4 c4 (CS12⁻ ∷ CCZ123 ∷ []) (CCZ123 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 2 2 (Toff304 ∷ Sb⁻0-1-2-3 ∷ []) (lem-comm-SBOXd⟨0·1·2·3⟩-TOFF304 c4) ▸
       at 3 1 (CS12⁻ ∷ []) (refl) ▸
       at 3 2 (CCZ123 ∷ CS12⁻ ∷ []) (lw4 c4 (CS12⁻ ∷ CCZ123 ∷ []) (CCZ123 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ CS12⁻ ∷ []) (Bx3-0412 ∷ Sb⁻0-1-2-3 ∷ [])
  b1 = at 4 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 0 4 (Bx3-0412 ∷ []) (sym (lem-beta-T-at0310243142 c4)) ▸ done


-- beta-T @0312243041: 8 steps
lem-beta-T-at0312243041 : Complete 4 → ⟪ (Bx3-2401 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ []) ⟫ʷ
lem-beta-T-at0312243041 c4 = run b0
  where
  b0 : Chain (Bx3-2401 ∷ []) (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-1402 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·2401⟩ c4) ▸
       at 1 1 (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ []) (lem-beta-T-at03243042 c4) ▸
       at 0 2 (Toff324 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff314 ∷ []) (Toff324 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 2 2 (Toff324 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff314 ∷ []) (Toff324 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 4 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- beta-T @0312243140: 8 steps
lem-beta-T-at0312243140 : Complete 4 → ⟪ (Bx3-2410 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ []) ⟫ʷ
lem-beta-T-at0312243140 c4 = run b0
  where
  b0 : Chain (Bx3-2410 ∷ []) (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-2401 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·2410⟩ c4) ▸
       at 1 1 (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ []) (lem-beta-T-at0312243041 c4) ▸
       at 0 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 1 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 3 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(3;2410): 14 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨3·2410⟩ : Complete 4 → ⟪ (Sb⁻0-1-2-3 ∷ Bx3-2410 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2410 ∷ Sb⁻0-1-2-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨3·2410⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb⁻0-1-2-3 ∷ Bx3-2410 ∷ []) (Toff324 ∷ CCZ013 ∷ CS12⁻ ∷ Toff324 ∷ CCZ013 ∷ [])
  b0 = at 1 1 (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ []) (lem-beta-T-at0312243140 c4) ▸
       at 0 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 2 (Toff324 ∷ CS12⁻ ∷ []) (lw0 c4 (CS12⁻ ∷ Toff324 ∷ []) (Toff324 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 1 1 (CS12⁻ ∷ []) (refl) ▸
       at 1 2 (CCZ013 ∷ CS12⁻ ∷ []) (lw4 c4 (CS12⁻ ∷ CCZ013 ∷ []) (CCZ013 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 2 1 (CS12⁻ ∷ []) (refl) ▸ done

  b1 : Chain (Toff324 ∷ CCZ013 ∷ CS12⁻ ∷ Toff324 ∷ CCZ013 ∷ []) (Bx3-2410 ∷ Sb⁻0-1-2-3 ∷ [])
  b1 = at 2 2 (Toff324 ∷ CS12⁻ ∷ []) (lw0 c4 (CS12⁻ ∷ Toff324 ∷ []) (Toff324 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 3 1 (CS12⁻ ∷ []) (refl) ▸
       at 3 2 (CCZ013 ∷ CS12⁻ ∷ []) (lw4 c4 (CS12⁻ ∷ CCZ013 ∷ []) (CCZ013 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 0 4 (Bx3-2410 ∷ []) (sym (lem-beta-T-at0312243140 c4)) ▸ done


-- auto CSd01 | BOX(1;2304) @3443: 7 steps
lem-auto-CSd01-∣-BOX⟨1·2304⟩-at3443 : Complete 4 → ⟪ (CS01⁻ ∷ Bx1-2403 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2403 ∷ CS01⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨1·2304⟩-at3443 c4 = run b0
  where
  b0 : Chain (CS01⁻ ∷ Bx1-2403 ∷ []) (Bx1-2403 ∷ CS01⁻ ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS01⁻ ∷ Sw34 ∷ []) (sym (c₂ (CS • CS • CS) (Swap ↑))) ▸
       at 2 2 (Bx1-2304 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·2403⟩ c4) ▸
       at 1 2 (Bx1-2304 ∷ CS01⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨1·2304⟩ c4) ▸
       at 0 2 (Bx1-2403 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·2304⟩ c4) ▸
       at 1 2 (CS01⁻ ∷ Sw34 ∷ []) (sym (c₂ (CS • CS • CS) (Swap ↑))) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CSd01 | BOX(1;2304) @12213443: 7 steps
lem-auto-CSd01-∣-BOX⟨1·2304⟩-at12213443 : Complete 4 → ⟪ (CS02⁻ ∷ Bx2-1403 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1403 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨1·2304⟩-at12213443 c4 = run b0
  where
  b0 : Chain (CS02⁻ ∷ Bx2-1403 ∷ []) (Bx2-1403 ∷ CS02⁻ ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS01⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd02 c4) ▸
       at 2 2 (Bx1-2403 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·1403⟩ c4) ▸
       at 1 2 (Bx1-2403 ∷ CS01⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨1·2304⟩-at3443 c4) ▸
       at 0 2 (Bx2-1403 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·2403⟩ c4) ▸
       at 1 2 (CS02⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd01 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CSd01 | BOX(1;2304) @0112203443: 7 steps
lem-auto-CSd01-∣-BOX⟨1·2304⟩-at0112203443 : Complete 4 → ⟪ (CS12⁻ ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CS12⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨1·2304⟩-at0112203443 c4 = run b0
  where
  b0 : Chain (CS12⁻ ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CS12⁻ ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS02⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS12⁻ ∷ []) (CS02⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx2-1403 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·0413⟩ c4) ▸
       at 1 2 (Bx2-1403 ∷ CS02⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨1·2304⟩-at12213443 c4) ▸
       at 0 2 (Bx2-0413 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1403⟩ c4) ▸
       at 1 2 (CS12⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS02⁻ ∷ []) (CS12⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(2;0413): 3 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0413⟩ : Complete 4 → ⟪ (Sb⁻0-1-2-3 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ Sb⁻0-1-2-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0413⟩ c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-2-3 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ Sb⁻0-1-2-3 ∷ [])
  b0 = at 0 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 2 (Bx2-0413 ∷ CS12⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨1·2304⟩-at0112203443 c4) ▸
       at 1 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸ done


-- auto CS01 | BOX(1;2304) @3443: 7 steps
lem-auto-CS01-∣-BOX⟨1·2304⟩-at3443 : Complete 4 → ⟪ (CS01 ∷ Bx1-2403 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2403 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨1·2304⟩-at3443 c4 = run b0
  where
  b0 : Chain (CS01 ∷ Bx1-2403 ∷ []) (Bx1-2403 ∷ CS01 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 2 2 (Bx1-2304 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·2403⟩ c4) ▸
       at 1 2 (Bx1-2304 ∷ CS01 ∷ []) (lem-auto-CS01-∣-BOX⟨1·2304⟩ c4) ▸
       at 0 2 (Bx1-2403 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·2304⟩ c4) ▸
       at 1 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CS01 | BOX(1;2304) @12213443: 7 steps
lem-auto-CS01-∣-BOX⟨1·2304⟩-at12213443 : Complete 4 → ⟪ (CS02 ∷ Bx2-1403 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1403 ∷ CS02 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨1·2304⟩-at12213443 c4 = run b0
  where
  b0 : Chain (CS02 ∷ Bx2-1403 ∷ []) (Bx2-1403 ∷ CS02 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS01 ∷ Sw12 ∷ []) (lem-nat-1-CS02 c4) ▸
       at 2 2 (Bx1-2403 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·1403⟩ c4) ▸
       at 1 2 (Bx1-2403 ∷ CS01 ∷ []) (lem-auto-CS01-∣-BOX⟨1·2304⟩-at3443 c4) ▸
       at 0 2 (Bx2-1403 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·2403⟩ c4) ▸
       at 1 2 (CS02 ∷ Sw12 ∷ []) (lem-nat-1-CS01 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CS01 | BOX(1;2304) @0112203443: 7 steps
lem-auto-CS01-∣-BOX⟨1·2304⟩-at0112203443 : Complete 4 → ⟪ (CS12 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CS12 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨1·2304⟩-at0112203443 c4 = run b0
  where
  b0 : Chain (CS12 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CS12 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS02 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx2-1403 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·0413⟩ c4) ▸
       at 1 2 (Bx2-1403 ∷ CS02 ∷ []) (lem-auto-CS01-∣-BOX⟨1·2304⟩-at12213443 c4) ▸
       at 0 2 (Bx2-0413 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1403⟩ c4) ▸
       at 1 2 (CS12 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS02 ∷ []) (CS12 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;2;3) | BOX(2;0413): 3 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0413⟩ : Complete 4 → ⟪ (Sb0-1-2-3 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ Sb0-1-2-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0413⟩ c4 = run b0
  where
  b0 : Chain (Sb0-1-2-3 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ Sb0-1-2-3 ∷ [])
  b0 = at 0 1 (CS12 ∷ []) (refl) ▸
       at 0 2 (Bx2-0413 ∷ CS12 ∷ []) (lem-auto-CS01-∣-BOX⟨1·2304⟩-at0112203443 c4) ▸
       at 1 1 (Sb0-1-2-3 ∷ []) (refl) ▸ done


-- beta-T @0412213043: 8 steps
lem-beta-T-at0412213043 : Complete 4 → ⟪ (Bx4-2103 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ []) ⟫ʷ
lem-beta-T-at0412213043 c4 = run b0
  where
  b0 : Chain (Bx4-2103 ∷ []) (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-2013 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·2103⟩ c4) ▸
       at 1 1 (Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ134 ∷ []) (lem-beta-T-at0412203143 c4) ▸
       at 0 2 (Toff412 ∷ Sw01 ∷ []) (lem-nat-0-TOFF402 c4) ▸
       at 1 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 2 2 (Toff412 ∷ Sw01 ∷ []) (lem-nat-0-TOFF402 c4) ▸
       at 3 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 4 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @0412213043: 5 steps
lem-sym23-at0412213043 : Complete 4 → ⟪ (Bx4-2103 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2013 ∷ []) ⟫ʷ
lem-sym23-at0412213043 c4 = run b0
  where
  b0 : Chain (Bx4-2103 ∷ []) (Bx4-2013 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-2013 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·2103⟩ c4) ▸
       at 1 1 (Bx4-2103 ∷ []) (lem-sym23-at0412203143 c4) ▸
       at 0 2 (Bx4-2013 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·2103⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | BOX(4;0213): 27 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨4·0213⟩ : Complete 4 → ⟪ (Bx0-1234 ∷ Bx4-0213 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0213 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨4·0213⟩ c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Bx0-1234 ∷ Bx4-0213 ∷ []) (Toff412 ∷ Bx0-1243 ∷ CCZ123 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ [])
  b0 = at 1 1 (Bx4-2013 ∷ []) (lem-sym12-at04103143 c4) ▸
       at 1 1 (Bx4-2103 ∷ []) (lem-sym23-at0412203143 c4) ▸
       at 1 1 (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ []) (lem-beta-T-at0412213043 c4) ▸
       at 0 0 (Toff412 ∷ Toff412 ∷ []) (lw0 c4 [] (Toff412 ∷ Toff412 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Toff412 ∷ []) (lw0 c4 (Toff412 ∷ []) (Toff412 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Toff412 ∷ []) (lw0 c4 (Toff412 ∷ []) (Toff412 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Bx0-1243 ∷ []) (lem-sym34 c4) ▸
       at 1 3 (Bx0-1243 ∷ CCZ123 ∷ []) (lem-T312-beta-at3443 c4) ▸ done

  b1 : Chain (Toff412 ∷ Bx0-1243 ∷ CCZ123 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ []) (Toff412 ∷ CCZ123 ∷ CCZ034 ∷ Toff412 ∷ Bx0-1243 ∷ CCZ123 ∷ CCZ034 ∷ [])
  b1 = at 1 1 (Bx0-1234 ∷ []) (lem-sym34-at3443 c4) ▸
       at 1 2 (CCZ123 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ123 c4) ▸
       at 2 2 (CCZ034 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ403 c4) ▸
       at 3 0 (Toff412 ∷ Toff412 ∷ []) (lw0 c4 [] (Toff412 ∷ Toff412 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Toff412 ∷ []) (lw0 c4 (Toff412 ∷ []) (Toff412 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Toff412 ∷ []) (lw0 c4 (Toff412 ∷ []) (Toff412 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Bx0-1243 ∷ []) (lem-sym34 c4) ▸
       at 4 3 (Bx0-1243 ∷ CCZ123 ∷ []) (lem-T312-beta-at3443 c4) ▸ done

  b2 : Chain (Toff412 ∷ CCZ123 ∷ CCZ034 ∷ Toff412 ∷ Bx0-1243 ∷ CCZ123 ∷ CCZ034 ∷ []) (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ Bx0-1234 ∷ [])
  b2 = at 4 1 (Bx0-1234 ∷ []) (lem-sym34-at3443 c4) ▸
       at 4 2 (CCZ123 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ123 c4) ▸
       at 5 2 (CCZ034 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ403 c4) ▸
       at 0 2 (CCZ123 ∷ Toff412 ∷ []) (lw0 c4 (Toff412 ∷ CCZ123 ∷ []) (CCZ123 ∷ Toff412 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ123 ∷ Toff412 ∷ []) (lw0 c4 (Toff412 ∷ CCZ123 ∷ []) (CCZ123 ∷ Toff412 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ123 ∷ CCZ034 ∷ []) (lem-auto-CCZ012-∣-CCZ342-at0410233142 c4) ▸
       at 1 2 (CCZ123 ∷ Toff412 ∷ []) (lw0 c4 (Toff412 ∷ CCZ123 ∷ []) (CCZ123 ∷ Toff412 ∷ []) tt tt Eq.refl) ▸
       at 0 2 [] (lw4 c4 (CCZ123 ∷ CCZ123 ∷ []) [] tt tt Eq.refl) ▸ done

  b3 : Chain (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ Bx0-1234 ∷ []) (Bx4-0213 ∷ Bx0-1234 ∷ [])
  b3 = at 0 4 (Bx4-2103 ∷ []) (sym (lem-beta-T-at0412213043 c4)) ▸
       at 0 1 (Bx4-2013 ∷ []) (lem-sym23-at0412213043 c4) ▸
       at 0 1 (Bx4-0213 ∷ []) (lem-sym12-at0412203143 c4) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(2;0413) @2332: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0413⟩-at2332 : Complete 4 → ⟪ (Sb⁻0-1-3-2 ∷ Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ Sb⁻0-1-3-2 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0413⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-3-2 ∷ Bx3-0412 ∷ []) (Bx3-0412 ∷ Sb⁻0-1-3-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·3·2⟩ c4) ▸
       at 2 2 (Bx2-0413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0412⟩ c4) ▸
       at 1 2 (Bx2-0413 ∷ Sb⁻0-1-2-3 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0413⟩ c4) ▸
       at 0 2 (Bx3-0412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0413⟩ c4) ▸
       at 1 2 (Sb⁻0-1-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·2·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


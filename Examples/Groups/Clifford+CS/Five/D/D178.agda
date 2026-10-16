{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D178 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0001 ; wl0002 ; wl0006 ; wl0007 ; wl0035 ; wl0036 ; wl0138 ; wl0139 ; wl0212 ; wl0283 ; wl0333 ; wl0353 ; wl0729 ; wl0731 ; wl0732 ; wl0759 ; wl0760 ; wl0761 ; wl0762 ; wl0763 ; wl0764 ; wl0765 ; wl0766 ; wl0767 ; wl0768 ; wl0769 ; wl0770 ; wl0771 ; wl0772 ; wl0773 ; wl0774 ; wl0775 ; wl0776 ; wl0777 ; wl0778 ; wl0779 ; wl0780 ; wl0781 ; wl0782 ; wl0783 ; wl0784 ; wl0785 ; wl0786 ; wp0043 ; wp0044 ; wp0126 ; wp0178 ; wp0348 ; wp0349 ; wp0351 ; wp0352 ; wp0365 ; wp0397 ; wp0398 ; wp0399 ; wp0400 ; wp0401 ; wp0402 ; wp0403 ; wp0404 ; wp0405 ; wp0406 ; wp0407 ; wp0408 ; wp0409 ; wp0410 ; wp0411)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-Cz-beta ; lem-beta-T-at243243 ; lem-sym23 ; lem-sym34 ; lem-sym34-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-sym23-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-SBsym-at0113203442 ; lem-T312-beta-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at243243 ; lem-beta-T-at233442 ; lem-sym23-at233442 ; lem-sym23-at2442 ; lem-sym34-at243243 ; lem-sym34-at2442)
open import Examples.Groups.Clifford+CS.Five.D.D160 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS02-at2332 ; lem-sym12-at04103143 ; lem-sym12-at0412203143 ; lem-sym23-at0412203143)
open import Examples.Groups.Clifford+CS.Five.D.D161 using (lem-auto-BOX⟨0·1234⟩-∣-CCZ123 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ403 ; lem-auto-CS01-∣-BOX⟨1·2304⟩ ; lem-auto-CSd01-∣-BOX⟨1·2304⟩ ; lem-beta-T-at0412203143)
open import Examples.Groups.Clifford+CS.Five.D.D173 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D174 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd02-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D177 using (lem-auto-CCZ012-∣-CCZ342-at0410233142 ; lem-auto-CCZ012-∣-TOFF342-at3443 ; lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at0412233041)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-0-CCZ134)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-TOFF402)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-2-BOX⟨2·0413⟩ ; lem-nat-2-BOX⟨3·0412⟩)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-1-CS01 ; lem-nat-1-CS02)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-0-BOX⟨2·0413⟩ ; lem-nat-0-BOX⟨2·1403⟩ ; lem-nat-1-CSd02 ; lem-nat-2-SBOX⟨0·1·23·4⟩ ; lem-nat-2-SBOX⟨0·1·32·4⟩ ; lem-nat-2-SBOX⟨0·1·4·2⟩ ; lem-nat-2-SBOX⟨0·1·4·3⟩ ; lem-nat-2-SBOXd⟨0·1·4·2⟩ ; lem-nat-2-SBOXd⟨0·1·4·3⟩ ; lem-nat-3-SBOX⟨0·1·32·4⟩ ; lem-nat-3-SBOX⟨0·1·3·2⟩ ; lem-nat-3-SBOX⟨0·1·42·3⟩ ; lem-nat-3-SBOX⟨0·1·4·2⟩ ; lem-nat-3-SBOXd⟨0·1·3·2⟩ ; lem-nat-3-SBOXd⟨0·1·4·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-1-CSd01 ; lem-nat-3-BOX⟨3·0412⟩ ; lem-nat-3-SBOX⟨3·0·2·1⟩ ; lem-nat-3-SBOXd⟨3·0·2·1⟩)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-2-SBOX⟨0·1·2·3⟩ ; lem-nat-2-SBOX⟨0·1·3·2⟩ ; lem-nat-2-SBOXd⟨0·1·2·3⟩ ; lem-nat-2-SBOXd⟨0·1·3·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-nat-1-BOX⟨1·2403⟩ ; lem-nat-1-BOX⟨2·1403⟩ ; lem-nat-3-BOX⟨1·2304⟩ ; lem-nat-3-BOX⟨1·2403⟩)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-2-BOX⟨4·0213⟩ ; lem-nat-2-BOX⟨4·0312⟩)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-2-SBOX⟨4·0·2·1⟩ ; lem-nat-2-SBOXd⟨4·0·2·1⟩ ; lem-nat-2-SBOXd⟨4·0·3·1⟩)
open import Examples.Groups.Clifford+CS.Five.D.R017 using (lem-nat-0-BOX⟨4·2103⟩ ; lem-nat-2-SBOX⟨4·0·3·1⟩ ; lem-nat-3-BOX⟨4·0312⟩ ; lem-nat-3-SBOX⟨4·0·2·1⟩ ; lem-nat-3-SBOXd⟨4·0·2·1⟩)
-- F4 CS12^0|K0^1: 131 steps
lem-F4-CS12ᵖ0∣K0ᵖ1 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS12ᵖ0∣K0ᵖ1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (run b16))))))))))))))))
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK40 ∷ []) (ι ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ [])
  b0 = at 3 1 (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ []) (wp0126 c4) ▸
       at 2 2 (ι ∷ X4 ∷ []) (zc) ▸
       at 1 2 (ι ∷ Sb0-1-42-3 ∷ []) (zc) ▸
       at 0 2 (ι ∷ X4 ∷ []) (zc) ▸
       at 2 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b1 : Chain (ι ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ []) (ι ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ S4⁻ ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ [])
  b1 = at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 1 (CS13⁻ ∷ []) (refl) ▸
       at 13 4 (S4⁻ ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (sym (wl0769 (lit c4))) ▸
       at 15 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 10 4 (S4⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (sym (wl0770 (lit c4))) ▸
       at 8 1 (CS13 ∷ []) (refl) ▸
       at 7 4 (S4⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ []) (sym (wl0771 (lit c4))) ▸
       at 9 1 (Sb0-1-3-2 ∷ []) (refl) ▸ done

  b2 : Chain (ι ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ S4⁻ ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ []) (ι ∷ X4 ∷ Toff014 ∷ X4 ∷ S4⁻ ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ [])
  b2 = at 4 4 (S4⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (sym (wl0770 (lit c4))) ▸
       at 2 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at243243 c4) ▸
       at 3 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 4 (S4⁻ ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (sym (wp0407 c4)) ▸
       at 7 4 (S4⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (sym (wp0408 c4)) ▸
       at 4 4 (S4⁻ ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (sym (wp0407 c4)) ▸ done

  b3 : Chain (ι ∷ X4 ∷ Toff014 ∷ X4 ∷ S4⁻ ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ [])
  b3 = at 1 4 (S4⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (sym (wp0408 c4)) ▸
       at 4 2 [] (wl0283 (lit c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸
       at 6 2 [] (wl0283 (lit c4)) ▸
       at 3 4 (Bx0-1423 ∷ []) (sym (lem-beta-T-at243243 c4)) ▸
       at 4 2 [] (wl0283 (lit c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸
       at 6 2 [] (wl0283 (lit c4)) ▸ done

  b4 : Chain (ι ∷ S4⁻ ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ [])
  b4 = at 7 2 [] (wl0283 (lit c4)) ▸
       at 3 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 1 (CS13⁻ ∷ []) (refl) ▸ done

  b5 : Chain (ι ∷ S4⁻ ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ X4 ∷ CS04 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ [])
  b5 = at 14 4 (CS04 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (sym (wp0397 c4)) ▸
       at 16 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 11 4 (CS04 ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (sym (wp0398 c4)) ▸
       at 9 1 (CS13 ∷ []) (refl) ▸
       at 8 4 (CS04 ∷ X4 ∷ CS13 ∷ X4 ∷ []) (sym (wp0399 c4)) ▸
       at 10 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 5 4 (CS04 ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (sym (wp0398 c4)) ▸
       at 3 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at243243 c4) ▸ done

  b6 : Chain (ι ∷ S4⁻ ∷ X4 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ X4 ∷ CS04 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ []) (ι ∷ S4⁻ ∷ CS04 ∷ X4 ∷ Toff014 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ [])
  b6 = at 4 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 4 (CS04 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (sym (wp0400 c4)) ▸
       at 8 4 (CS04 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (sym (wp0401 c4)) ▸
       at 5 4 (CS04 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (sym (wp0400 c4)) ▸
       at 2 4 (CS04 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (sym (wp0401 c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸ done

  b7 : Chain (ι ∷ S4⁻ ∷ CS04 ∷ X4 ∷ Toff014 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ []) (ι ∷ S4⁻ ∷ CS04 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ [])
  b7 = at 6 2 [] (wl0283 (lit c4)) ▸
       at 7 2 [] (wl0283 (lit c4)) ▸
       at 4 4 (Bx0-1423 ∷ []) (sym (lem-beta-T-at243243 c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸
       at 6 2 [] (wl0283 (lit c4)) ▸
       at 7 2 [] (wl0283 (lit c4)) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸
       at 4 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done

  b8 : Chain (ι ∷ S4⁻ ∷ CS04 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ []) (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS04 ∷ K0 ∷ CS04 ∷ [])
  b8 = at 5 2 (K0 ∷ X4 ∷ []) (sym (wl0772 (lit c4))) ▸
       at 4 2 (K0 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at243243 c4) ▸
       at 3 2 (K0 ∷ X4 ∷ []) (sym (wl0772 (lit c4))) ▸
       at 5 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b9 : Chain (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS04 ∷ K0 ∷ CS04 ∷ []) (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ CS04 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K0 ∷ CS04 ∷ [])
  b9 = at 17 1 (CS13⁻ ∷ []) (refl) ▸
       at 16 4 (CS04 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (sym (wp0397 c4)) ▸
       at 18 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 13 4 (CS04 ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (sym (wp0398 c4)) ▸
       at 11 1 (CS13 ∷ []) (refl) ▸
       at 10 4 (CS04 ∷ X4 ∷ CS13 ∷ X4 ∷ []) (sym (wp0399 c4)) ▸
       at 12 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 7 4 (CS04 ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (sym (wp0398 c4)) ▸ done

  b10 : Chain (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ CS04 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K0 ∷ CS04 ∷ []) (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K0 ∷ CS04 ∷ [])
  b10 = at 5 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at243243 c4) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 13 4 (CS04 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (sym (wp0400 c4)) ▸
       at 10 4 (CS04 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (sym (wp0401 c4)) ▸
       at 7 4 (CS04 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (sym (wp0400 c4)) ▸
       at 4 4 (CS04 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (sym (wp0401 c4)) ▸ done

  b11 : Chain (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K0 ∷ CS04 ∷ []) (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K0 ∷ CS04 ∷ [])
  b11 = at 7 2 [] (wl0283 (lit c4)) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 6 4 (Bx0-1423 ∷ []) (sym (lem-beta-T-at243243 c4)) ▸
       at 7 2 [] (wl0283 (lit c4)) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸ done

  b12 : Chain (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K0 ∷ CS04 ∷ []) (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS04 ∷ [])
  b12 = at 6 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 7 2 (K0 ∷ X4 ∷ []) (sym (wl0772 (lit c4))) ▸
       at 6 2 (K0 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at243243 c4) ▸
       at 5 2 (K0 ∷ X4 ∷ []) (sym (wl0772 (lit c4))) ▸
       at 7 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b13 : Chain (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS04 ∷ []) (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ [])
  b13 = at 17 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 19 1 (CS13⁻ ∷ []) (refl) ▸
       at 18 4 (CS04 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (sym (wp0397 c4)) ▸
       at 20 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 15 4 (CS04 ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (sym (wp0398 c4)) ▸
       at 13 1 (CS13 ∷ []) (refl) ▸
       at 12 4 (CS04 ∷ X4 ∷ CS13 ∷ X4 ∷ []) (sym (wp0399 c4)) ▸
       at 14 1 (Sb0-1-3-2 ∷ []) (refl) ▸ done

  b14 : Chain (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ []) (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ X4 ∷ Toff014 ∷ X4 ∷ CS04 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ [])
  b14 = at 9 4 (CS04 ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (sym (wp0398 c4)) ▸
       at 7 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at243243 c4) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 4 (CS04 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (sym (wp0400 c4)) ▸
       at 12 4 (CS04 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (sym (wp0401 c4)) ▸
       at 9 4 (CS04 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (sym (wp0400 c4)) ▸ done

  b15 : Chain (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ X4 ∷ Toff014 ∷ X4 ∷ CS04 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ []) (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ [])
  b15 = at 6 4 (CS04 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (sym (wp0401 c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸
       at 11 2 [] (wl0283 (lit c4)) ▸
       at 8 4 (Bx0-1423 ∷ []) (sym (lem-beta-T-at243243 c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸
       at 11 2 [] (wl0283 (lit c4)) ▸ done

  b16 : Chain (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ []) (CK40 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b16 = at 12 2 [] (wl0283 (lit c4)) ▸
       at 8 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 0 7 (CK40 ∷ []) (sym (wp0126 c4)) ▸ done


-- F4 CS12^0|K1^1: 221 steps
lem-F4-CS12ᵖ0∣K1ᵖ1 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS12ᵖ0∣K1ᵖ1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (run b27)))))))))))))))))))))))))))
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ []) (ι ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ [])
  b0 = at 3 1 (ι1 ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ []) (wp0178 c4) ▸
       at 3 1 (ι ∷ []) (uₛ (iI ↑) (iI) Eq.refl) ▸
       at 2 2 (ι ∷ X4 ∷ []) (zc) ▸
       at 1 2 (ι ∷ Sb0-1-42-3 ∷ []) (zc) ▸
       at 0 2 (ι ∷ X4 ∷ []) (zc) ▸
       at 2 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b1 : Chain (ι ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ []) (ι ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ S4⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ [])
  b1 = at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 1 (CS13⁻ ∷ []) (refl) ▸
       at 13 4 (S4⁻ ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (sym (wl0769 (lit c4))) ▸
       at 15 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 10 4 (S4⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (sym (wl0770 (lit c4))) ▸
       at 8 1 (CS13 ∷ []) (refl) ▸
       at 7 4 (S4⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ []) (sym (wl0771 (lit c4))) ▸ done

  b2 : Chain (ι ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ S4⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ []) (ι ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ S4⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ [])
  b2 = at 9 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 4 4 (S4⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (sym (wl0770 (lit c4))) ▸
       at 2 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at243243 c4) ▸
       at 3 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 4 (S4⁻ ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (sym (wp0407 c4)) ▸
       at 7 4 (S4⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (sym (wp0408 c4)) ▸ done

  b3 : Chain (ι ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ S4⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ [])
  b3 = at 4 4 (S4⁻ ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (sym (wp0407 c4)) ▸
       at 1 4 (S4⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (sym (wp0408 c4)) ▸
       at 4 2 [] (wl0283 (lit c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸
       at 6 2 [] (wl0283 (lit c4)) ▸
       at 3 4 (Bx0-1423 ∷ []) (sym (lem-beta-T-at243243 c4)) ▸
       at 4 2 [] (wl0283 (lit c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸ done

  b4 : Chain (ι ∷ S4⁻ ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ [])
  b4 = at 6 2 [] (wl0283 (lit c4)) ▸
       at 7 2 [] (wl0283 (lit c4)) ▸
       at 3 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b5 : Chain (ι ∷ S4⁻ ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ CS14 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ [])
  b5 = at 15 1 (CS13⁻ ∷ []) (refl) ▸
       at 14 4 (CS14 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (sym (wl0759 (lit c4))) ▸
       at 16 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 11 4 (CS14 ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (sym (wl0760 (lit c4))) ▸
       at 9 1 (CS13 ∷ []) (refl) ▸
       at 8 4 (CS14 ∷ X4 ∷ CS13 ∷ X4 ∷ []) (sym (wl0761 (lit c4))) ▸
       at 10 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 5 4 (CS14 ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (sym (wl0760 (lit c4))) ▸ done

  b6 : Chain (ι ∷ S4⁻ ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ CS14 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX23 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX23 ∷ CS02 ∷ X4 ∷ CS14 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ [])
  b6 = at 3 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at243243 c4) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 12 1 (CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ []) (wl0353 (lit c4)) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 16 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 19 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b7 : Chain (ι ∷ S4⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX23 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX23 ∷ CS02 ∷ X4 ∷ CS14 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ CS14 ∷ X4 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX23 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ [])
  b7 = at 22 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 23 4 (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (sym (wp0365 c4)) ▸
       at 20 4 (CS14 ∷ X4 ∷ CX23 ∷ X4 ∷ []) (sym (wl0762 (lit c4))) ▸
       at 17 4 (CS14 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (sym (wp0348 c4)) ▸
       at 14 4 (CS14 ∷ X4 ∷ CX23 ∷ X4 ∷ []) (sym (wl0762 (lit c4))) ▸
       at 11 4 (CS14 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (sym (wp0349 c4)) ▸
       at 14 2 [] (wl0283 (lit c4)) ▸
       at 15 2 [] (wl0283 (lit c4)) ▸ done

  b8 : Chain (ι ∷ S4⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ CS14 ∷ X4 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX23 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX23 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX23 ∷ CS02 ∷ X4 ∷ CS14 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ [])
  b8 = at 16 2 [] (wl0283 (lit c4)) ▸
       at 17 2 [] (wl0283 (lit c4)) ▸
       at 13 5 (CCZ023 ∷ []) (sym (wl0353 (lit c4))) ▸
       at 8 4 (CS14 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (sym (wp0402 c4)) ▸
       at 6 1 (CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ []) (wl0353 (lit c4)) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b9 : Chain (ι ∷ S4⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX23 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX23 ∷ CS02 ∷ X4 ∷ CS14 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ CS14 ∷ X4 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX23 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ [])
  b9 = at 16 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 17 4 (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (sym (wp0365 c4)) ▸
       at 14 4 (CS14 ∷ X4 ∷ CX23 ∷ X4 ∷ []) (sym (wl0762 (lit c4))) ▸
       at 11 4 (CS14 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (sym (wp0348 c4)) ▸
       at 8 4 (CS14 ∷ X4 ∷ CX23 ∷ X4 ∷ []) (sym (wl0762 (lit c4))) ▸
       at 5 4 (CS14 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (sym (wp0349 c4)) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸ done

  b10 : Chain (ι ∷ S4⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ CS14 ∷ X4 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX23 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ CS14 ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ [])
  b10 = at 10 2 [] (wl0283 (lit c4)) ▸
       at 11 2 [] (wl0283 (lit c4)) ▸
       at 7 5 (CCZ023 ∷ []) (sym (wl0353 (lit c4))) ▸
       at 2 4 (CS14 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (sym (wp0402 c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸
       at 6 2 [] (wl0283 (lit c4)) ▸
       at 7 2 [] (wl0283 (lit c4)) ▸
       at 4 4 (Bx0-1423 ∷ []) (sym (lem-beta-T-at243243 c4)) ▸ done

  b11 : Chain (ι ∷ S4⁻ ∷ CS14 ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ CS14 ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ [])
  b11 = at 5 2 [] (wl0283 (lit c4)) ▸
       at 6 2 [] (wl0283 (lit c4)) ▸
       at 7 2 [] (wl0283 (lit c4)) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸
       at 4 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 4 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b12 : Chain (ι ∷ S4⁻ ∷ CS14 ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ CS14 ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS14 ∷ [])
  b12 = at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 1 (CS13 ∷ []) (refl) ▸
       at 16 1 (CS13⁻ ∷ []) (refl) ▸
       at 9 12 (K1 ∷ CS14 ∷ K1 ∷ X4 ∷ CS13 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (sym (wl0773 (lit c4))) ▸
       at 13 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 19 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 6 6 (K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (sym (wl0774 (lit c4))) ▸ done

  b13 : Chain (ι ∷ S4⁻ ∷ CS14 ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ CS14 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ X4 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ X4 ∷ CS14 ∷ K1 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS14 ∷ [])
  b13 = at 4 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at243243 c4) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 13 2 (K1 ∷ CCZ023 ∷ []) (wl0775 (lit c4)) ▸
       at 12 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 14 1 (CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ []) (wl0353 (lit c4)) ▸ done

  b14 : Chain (ι ∷ S4⁻ ∷ CS14 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ X4 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ X4 ∷ CS14 ∷ K1 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ CS14 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ X4 ∷ CS03 ∷ X4 ∷ CS14 ∷ X4 ∷ CX23 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX23 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ K1 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS14 ∷ [])
  b14 = at 15 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 21 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 24 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 25 4 (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (sym (wp0365 c4)) ▸
       at 22 4 (CS14 ∷ X4 ∷ CX23 ∷ X4 ∷ []) (sym (wl0762 (lit c4))) ▸
       at 19 4 (CS14 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (sym (wp0348 c4)) ▸
       at 16 4 (CS14 ∷ X4 ∷ CX23 ∷ X4 ∷ []) (sym (wl0762 (lit c4))) ▸ done

  b15 : Chain (ι ∷ S4⁻ ∷ CS14 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ X4 ∷ CS03 ∷ X4 ∷ CS14 ∷ X4 ∷ CX23 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX23 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ K1 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ CS14 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CS14 ∷ X4 ∷ K1 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS14 ∷ [])
  b15 = at 13 4 (CS14 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (sym (wp0349 c4)) ▸
       at 16 2 [] (wl0283 (lit c4)) ▸
       at 17 2 [] (wl0283 (lit c4)) ▸
       at 18 2 [] (wl0283 (lit c4)) ▸
       at 19 2 [] (wl0283 (lit c4)) ▸
       at 15 5 (CCZ023 ∷ []) (sym (wl0353 (lit c4))) ▸
       at 16 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 15 2 (K1 ∷ CCZ023 ∷ []) (wl0775 (lit c4)) ▸ done

  b16 : Chain (ι ∷ S4⁻ ∷ CS14 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CS14 ∷ X4 ∷ K1 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ CS14 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX23 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ X4 ∷ CS14 ∷ K1 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS14 ∷ [])
  b16 = at 14 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 9 6 (K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (sym (wp0409 c4)) ▸
       at 8 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 7 2 (K1 ∷ CCZ023 ∷ []) (wl0775 (lit c4)) ▸
       at 6 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 8 1 (CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ []) (wl0353 (lit c4)) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b17 : Chain (ι ∷ S4⁻ ∷ CS14 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX23 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ X4 ∷ CS14 ∷ K1 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ CS14 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CS14 ∷ X4 ∷ CS03 ∷ CX23 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX23 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ K1 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS14 ∷ [])
  b17 = at 15 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 19 4 (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (sym (wp0365 c4)) ▸
       at 16 4 (CS14 ∷ X4 ∷ CX23 ∷ X4 ∷ []) (sym (wl0762 (lit c4))) ▸
       at 13 4 (CS14 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (sym (wp0348 c4)) ▸
       at 10 4 (CS14 ∷ X4 ∷ CX23 ∷ X4 ∷ []) (sym (wl0762 (lit c4))) ▸
       at 7 4 (CS14 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (sym (wp0349 c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸ done

  b18 : Chain (ι ∷ S4⁻ ∷ CS14 ∷ X4 ∷ Toff014 ∷ X4 ∷ K1 ∷ CS14 ∷ X4 ∷ CS03 ∷ CX23 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX23 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ K1 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS14 ∷ [])
  b18 = at 11 2 [] (wl0283 (lit c4)) ▸
       at 12 2 [] (wl0283 (lit c4)) ▸
       at 13 2 [] (wl0283 (lit c4)) ▸
       at 9 5 (CCZ023 ∷ []) (sym (wl0353 (lit c4))) ▸
       at 10 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 9 2 (K1 ∷ CCZ023 ∷ []) (wl0775 (lit c4)) ▸
       at 8 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 3 6 (K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (sym (wp0409 c4)) ▸ done

  b19 : Chain (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS14 ∷ [])
  b19 = at 8 2 [] (wl0283 (lit c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸
       at 7 4 (Bx0-1423 ∷ []) (sym (lem-beta-T-at243243 c4)) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸
       at 11 2 [] (wl0283 (lit c4)) ▸ done

  b20 : Chain (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ CS14 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ [])
  b20 = at 7 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 7 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 17 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 19 1 (CS13⁻ ∷ []) (refl) ▸
       at 18 4 (CS14 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (sym (wl0759 (lit c4))) ▸ done

  b21 : Chain (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ CS14 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ X4 ∷ CS14 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ [])
  b21 = at 20 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 15 4 (CS14 ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (sym (wl0760 (lit c4))) ▸
       at 13 1 (CS13 ∷ []) (refl) ▸
       at 12 4 (CS14 ∷ X4 ∷ CS13 ∷ X4 ∷ []) (sym (wl0761 (lit c4))) ▸
       at 14 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 9 4 (CS14 ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (sym (wl0760 (lit c4))) ▸
       at 7 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at243243 c4) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b22 : Chain (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ X4 ∷ CS14 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ []) (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX23 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX23 ∷ X4 ∷ CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ [])
  b22 = at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 16 1 (CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ []) (wl0353 (lit c4)) ▸
       at 17 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 20 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 23 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 26 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 27 4 (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (sym (wp0365 c4)) ▸ done

  b23 : Chain (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX23 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX23 ∷ X4 ∷ CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ []) (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ CS14 ∷ X4 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ [])
  b23 = at 24 4 (CS14 ∷ X4 ∷ CX23 ∷ X4 ∷ []) (sym (wl0762 (lit c4))) ▸
       at 21 4 (CS14 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (sym (wp0348 c4)) ▸
       at 18 4 (CS14 ∷ X4 ∷ CX23 ∷ X4 ∷ []) (sym (wl0762 (lit c4))) ▸
       at 15 4 (CS14 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (sym (wp0349 c4)) ▸
       at 18 2 [] (wl0283 (lit c4)) ▸
       at 19 2 [] (wl0283 (lit c4)) ▸
       at 20 2 [] (wl0283 (lit c4)) ▸
       at 21 2 [] (wl0283 (lit c4)) ▸ done

  b24 : Chain (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ CS14 ∷ X4 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ []) (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX23 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX23 ∷ X4 ∷ CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ [])
  b24 = at 17 5 (CCZ023 ∷ []) (sym (wl0353 (lit c4))) ▸
       at 12 4 (CS14 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (sym (wp0402 c4)) ▸
       at 10 1 (CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ []) (wl0353 (lit c4)) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 17 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 20 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 21 4 (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (sym (wp0365 c4)) ▸ done

  b25 : Chain (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX23 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX23 ∷ X4 ∷ CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ []) (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Toff014 ∷ X4 ∷ CS14 ∷ X4 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ [])
  b25 = at 18 4 (CS14 ∷ X4 ∷ CX23 ∷ X4 ∷ []) (sym (wl0762 (lit c4))) ▸
       at 15 4 (CS14 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (sym (wp0348 c4)) ▸
       at 12 4 (CS14 ∷ X4 ∷ CX23 ∷ X4 ∷ []) (sym (wl0762 (lit c4))) ▸
       at 9 4 (CS14 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (sym (wp0349 c4)) ▸
       at 12 2 [] (wl0283 (lit c4)) ▸
       at 13 2 [] (wl0283 (lit c4)) ▸
       at 14 2 [] (wl0283 (lit c4)) ▸
       at 15 2 [] (wl0283 (lit c4)) ▸ done

  b26 : Chain (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Toff014 ∷ X4 ∷ CS14 ∷ X4 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ []) (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ [])
  b26 = at 11 5 (CCZ023 ∷ []) (sym (wl0353 (lit c4))) ▸
       at 6 4 (CS14 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (sym (wp0402 c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸
       at 11 2 [] (wl0283 (lit c4)) ▸
       at 8 4 (Bx0-1423 ∷ []) (sym (lem-beta-T-at243243 c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸ done

  b27 : Chain (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ []) (CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b27 = at 11 2 [] (wl0283 (lit c4)) ▸
       at 12 2 [] (wl0283 (lit c4)) ▸
       at 8 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 0 1 (ι1 ∷ []) (uₛ (iI) (iI ↑) Eq.refl) ▸
       at 0 7 (CK41 ∷ []) (sym (wp0178 c4)) ▸ done


-- F4 CS12^0|K2^1: 185 steps
lem-F4-CS12ᵖ0∣K2ᵖ1 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS12ᵖ0∣K2ᵖ1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (run b23)))))))))))))))))))))))
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK42 ∷ []) (ι ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ [])
  b0 = at 3 1 (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ []) (wl0729 (lit c4)) ▸
       at 2 2 (ι ∷ X4 ∷ []) (zc) ▸
       at 1 2 (ι ∷ Sb0-1-42-3 ∷ []) (zc) ▸
       at 0 2 (ι ∷ X4 ∷ []) (zc) ▸
       at 2 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b1 : Chain (ι ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ []) (ι ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ S4⁻ ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ [])
  b1 = at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 1 (CS13⁻ ∷ []) (refl) ▸
       at 13 4 (S4⁻ ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (sym (wl0769 (lit c4))) ▸
       at 15 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 10 4 (S4⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (sym (wl0770 (lit c4))) ▸
       at 8 1 (CS13 ∷ []) (refl) ▸
       at 7 4 (S4⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ []) (sym (wl0771 (lit c4))) ▸
       at 9 1 (Sb0-1-3-2 ∷ []) (refl) ▸ done

  b2 : Chain (ι ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ S4⁻ ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ []) (ι ∷ X4 ∷ Toff014 ∷ X4 ∷ S4⁻ ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ [])
  b2 = at 4 4 (S4⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (sym (wl0770 (lit c4))) ▸
       at 2 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at243243 c4) ▸
       at 3 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 4 (S4⁻ ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (sym (wp0407 c4)) ▸
       at 7 4 (S4⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (sym (wp0408 c4)) ▸
       at 4 4 (S4⁻ ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (sym (wp0407 c4)) ▸ done

  b3 : Chain (ι ∷ X4 ∷ Toff014 ∷ X4 ∷ S4⁻ ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ [])
  b3 = at 1 4 (S4⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (sym (wp0408 c4)) ▸
       at 4 2 [] (wl0283 (lit c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸
       at 6 2 [] (wl0283 (lit c4)) ▸
       at 3 4 (Bx0-1423 ∷ []) (sym (lem-beta-T-at243243 c4)) ▸
       at 4 2 [] (wl0283 (lit c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸
       at 6 2 [] (wl0283 (lit c4)) ▸ done

  b4 : Chain (ι ∷ S4⁻ ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ [])
  b4 = at 7 2 [] (wl0283 (lit c4)) ▸
       at 3 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 1 (CS13⁻ ∷ []) (refl) ▸ done

  b5 : Chain (ι ∷ S4⁻ ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ X4 ∷ CS24 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ [])
  b5 = at 14 4 (CS24 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (sym (wl0763 (lit c4))) ▸
       at 16 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 11 4 (CS24 ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (sym (wl0764 (lit c4))) ▸
       at 9 1 (CS13 ∷ []) (refl) ▸
       at 8 4 (CS24 ∷ X4 ∷ CS13 ∷ X4 ∷ []) (sym (wl0765 (lit c4))) ▸
       at 10 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 5 4 (CS24 ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (sym (wl0764 (lit c4))) ▸
       at 3 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at243243 c4) ▸ done

  b6 : Chain (ι ∷ S4⁻ ∷ X4 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ X4 ∷ CS24 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ []) (ι ∷ S4⁻ ∷ CS24 ∷ X4 ∷ Toff014 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ [])
  b6 = at 4 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 4 (CS24 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (sym (wp0403 c4)) ▸
       at 8 4 (CS24 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (sym (wp0404 c4)) ▸
       at 5 4 (CS24 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (sym (wp0403 c4)) ▸
       at 2 4 (CS24 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (sym (wp0404 c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸ done

  b7 : Chain (ι ∷ S4⁻ ∷ CS24 ∷ X4 ∷ Toff014 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ []) (ι ∷ S4⁻ ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ [])
  b7 = at 6 2 [] (wl0283 (lit c4)) ▸
       at 7 2 [] (wl0283 (lit c4)) ▸
       at 4 4 (Bx0-1423 ∷ []) (sym (lem-beta-T-at243243 c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸
       at 6 2 [] (wl0283 (lit c4)) ▸
       at 7 2 [] (wl0283 (lit c4)) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸
       at 4 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done

  b8 : Chain (ι ∷ S4⁻ ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ []) (ι ∷ S4⁻ ∷ CS24 ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ K2 ∷ CS24 ∷ K2 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS24 ∷ [])
  b8 = at 4 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 16 1 (CS13⁻ ∷ []) (refl) ▸
       at 15 6 (K2 ∷ CS24 ∷ K2 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (sym (wl0776 (lit c4))) ▸
       at 19 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸ done

  b9 : Chain (ι ∷ S4⁻ ∷ CS24 ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ K2 ∷ CS24 ∷ K2 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS24 ∷ []) (ι ∷ S4⁻ ∷ CS24 ∷ X4 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CS24 ∷ K2 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS24 ∷ [])
  b9 = at 12 6 (K2 ∷ CS24 ∷ K2 ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (sym (wl0777 (lit c4))) ▸
       at 10 1 (CS13 ∷ []) (refl) ▸
       at 9 6 (K2 ∷ CS24 ∷ K2 ∷ X4 ∷ CS13 ∷ X4 ∷ []) (sym (wl0778 (lit c4))) ▸
       at 13 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 6 6 (K2 ∷ CS24 ∷ K2 ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (sym (wl0777 (lit c4))) ▸
       at 4 1 (Bx0-1432 ∷ []) (lem-sym34-at243243 c4) ▸
       at 4 1 (Bx0-1342 ∷ []) (lem-sym23-at2442 c4) ▸
       at 4 1 (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-beta-T-at233442 c4) ▸ done

  b10 : Chain (ι ∷ S4⁻ ∷ CS24 ∷ X4 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CS24 ∷ K2 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS24 ∷ []) (ι ∷ S4⁻ ∷ CS24 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ X4 ∷ K0 ∷ CCZ013 ∷ K0⁻ ∷ X4 ∷ CS24 ∷ K2 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS24 ∷ [])
  b10 = at 5 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 12 6 (K2 ∷ CS24 ∷ K2 ∷ X4 ∷ CCZ024 ∷ X4 ∷ []) (sym (wp0410 c4)) ▸
       at 11 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 10 2 (K2 ∷ Toff013 ∷ []) (sym (wl0779 (lit c4))) ▸
       at 9 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 11 1 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (sym (wl0780 (lit c4))) ▸ done

  b11 : Chain (ι ∷ S4⁻ ∷ CS24 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ X4 ∷ K0 ∷ CCZ013 ∷ K0⁻ ∷ X4 ∷ CS24 ∷ K2 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS24 ∷ []) (ι ∷ S4⁻ ∷ CS24 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ CS24 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS24 ∷ [])
  b11 = at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 16 4 (CS24 ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) (sym (wl0781 (lit c4))) ▸
       at 14 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl0333 (lit c4)) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 21 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 24 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b12 : Chain (ι ∷ S4⁻ ∷ CS24 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ CS24 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS24 ∷ []) (ι ∷ S4⁻ ∷ CS24 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ CS24 ∷ X4 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS24 ∷ [])
  b12 = at 25 4 (CS24 ∷ X4 ∷ CS01 ∷ X4 ∷ []) (sym (wp0411 c4)) ▸
       at 22 4 (CS24 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (sym (wl0782 (lit c4))) ▸
       at 19 4 (CS24 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (sym (wp0351 c4)) ▸
       at 16 4 (CS24 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (sym (wl0782 (lit c4))) ▸
       at 13 4 (CS24 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (sym (wp0352 c4)) ▸
       at 16 2 [] (wl0283 (lit c4)) ▸
       at 17 2 [] (wl0283 (lit c4)) ▸
       at 18 2 [] (wl0283 (lit c4)) ▸ done

  b13 : Chain (ι ∷ S4⁻ ∷ CS24 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ CS24 ∷ X4 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS24 ∷ []) (ι ∷ S4⁻ ∷ CS24 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CS24 ∷ X4 ∷ K2 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS24 ∷ [])
  b13 = at 19 2 [] (wl0283 (lit c4)) ▸
       at 15 5 (CCZ013 ∷ []) (sym (wl0333 (lit c4))) ▸
       at 10 4 (CS24 ∷ X4 ∷ K0 ∷ X4 ∷ []) (sym (wl0783 (lit c4))) ▸
       at 13 2 [] (wl0283 (lit c4)) ▸
       at 14 2 [] (wl0283 (lit c4)) ▸
       at 12 3 (Toff013 ∷ []) (wl0780 (lit c4)) ▸
       at 13 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 12 2 (K2 ∷ Toff013 ∷ []) (sym (wl0779 (lit c4))) ▸ done

  b14 : Chain (ι ∷ S4⁻ ∷ CS24 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ K2 ∷ CS24 ∷ X4 ∷ K2 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS24 ∷ []) (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ CS24 ∷ K2 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS24 ∷ [])
  b14 = at 11 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 6 6 (K2 ∷ CS24 ∷ K2 ∷ X4 ∷ CCZ024 ∷ X4 ∷ []) (sym (wp0410 c4)) ▸
       at 5 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 4 2 (K2 ∷ Toff013 ∷ []) (sym (wl0779 (lit c4))) ▸
       at 3 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 5 1 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (sym (wl0780 (lit c4))) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b15 : Chain (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ CS24 ∷ K2 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS24 ∷ []) (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ CS24 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS24 ∷ [])
  b15 = at 10 4 (CS24 ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) (sym (wl0781 (lit c4))) ▸
       at 8 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl0333 (lit c4)) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 19 4 (CS24 ∷ X4 ∷ CS01 ∷ X4 ∷ []) (sym (wp0411 c4)) ▸
       at 16 4 (CS24 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (sym (wl0782 (lit c4))) ▸ done

  b16 : Chain (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ CS24 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS24 ∷ []) (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ CS24 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS24 ∷ [])
  b16 = at 13 4 (CS24 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (sym (wp0351 c4)) ▸
       at 10 4 (CS24 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (sym (wl0782 (lit c4))) ▸
       at 7 4 (CS24 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (sym (wp0352 c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸
       at 11 2 [] (wl0283 (lit c4)) ▸
       at 12 2 [] (wl0283 (lit c4)) ▸
       at 13 2 [] (wl0283 (lit c4)) ▸
       at 9 5 (CCZ013 ∷ []) (sym (wl0333 (lit c4))) ▸ done

  b17 : Chain (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ X4 ∷ K0 ∷ X4 ∷ CS24 ∷ X4 ∷ CCZ013 ∷ X4 ∷ X4 ∷ K0⁻ ∷ X4 ∷ K2 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS24 ∷ []) (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ X4 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS24 ∷ [])
  b17 = at 4 4 (CS24 ∷ X4 ∷ K0 ∷ X4 ∷ []) (sym (wl0783 (lit c4))) ▸
       at 7 2 [] (wl0283 (lit c4)) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸
       at 6 3 (Toff013 ∷ []) (wl0780 (lit c4)) ▸
       at 7 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 6 2 (K2 ∷ Toff013 ∷ []) (sym (wl0779 (lit c4))) ▸
       at 5 2 (K2 ∷ X4 ∷ []) (sym (c₃ (K ↑ ↑) (X ↑))) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸ done

  b18 : Chain (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ X4 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff013 ∷ X4 ∷ X4 ∷ CCZ024 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS24 ∷ []) (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS24 ∷ [])
  b18 = at 9 2 [] (wl0283 (lit c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸
       at 7 4 (Bx0-1342 ∷ []) (sym (lem-beta-T-at233442 c4)) ▸
       at 7 1 (Bx0-1432 ∷ []) (lem-sym23-at233442 c4) ▸
       at 7 1 (Bx0-1423 ∷ []) (lem-sym34-at2442 c4) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸ done

  b19 : Chain (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS24 ∷ []) (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ CS24 ∷ [])
  b19 = at 11 2 [] (wl0283 (lit c4)) ▸
       at 7 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 7 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 17 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 19 1 (CS13⁻ ∷ []) (refl) ▸ done

  b20 : Chain (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ CS24 ∷ []) (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ X4 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ X4 ∷ CS24 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ [])
  b20 = at 18 4 (CS24 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (sym (wl0763 (lit c4))) ▸
       at 20 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 15 4 (CS24 ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (sym (wl0764 (lit c4))) ▸
       at 13 1 (CS13 ∷ []) (refl) ▸
       at 12 4 (CS24 ∷ X4 ∷ CS13 ∷ X4 ∷ []) (sym (wl0765 (lit c4))) ▸
       at 14 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 9 4 (CS24 ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (sym (wl0764 (lit c4))) ▸
       at 7 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at243243 c4) ▸ done

  b21 : Chain (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ X4 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ X4 ∷ CS24 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ []) (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ X4 ∷ Toff014 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ [])
  b21 = at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 4 (CS24 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (sym (wp0403 c4)) ▸
       at 12 4 (CS24 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (sym (wp0404 c4)) ▸
       at 9 4 (CS24 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (sym (wp0403 c4)) ▸
       at 6 4 (CS24 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (sym (wp0404 c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸ done

  b22 : Chain (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ X4 ∷ Toff014 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ []) (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b22 = at 10 2 [] (wl0283 (lit c4)) ▸
       at 11 2 [] (wl0283 (lit c4)) ▸
       at 8 4 (Bx0-1423 ∷ []) (sym (lem-beta-T-at243243 c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸
       at 11 2 [] (wl0283 (lit c4)) ▸
       at 12 2 [] (wl0283 (lit c4)) ▸
       at 8 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done

  b23 : Chain (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b23 = at 0 7 (CK42 ∷ []) (sym (wl0729 (lit c4))) ▸ done


-- F4 CS12^0|K3^1: 131 steps
lem-F4-CS12ᵖ0∣K3ᵖ1 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS12ᵖ0∣K3ᵖ1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (run b16))))))))))))))))
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK43 ∷ []) (ι ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ [])
  b0 = at 3 1 (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ []) (wl0731 (lit c4)) ▸
       at 2 2 (ι ∷ X4 ∷ []) (zc) ▸
       at 1 2 (ι ∷ Sb0-1-42-3 ∷ []) (zc) ▸
       at 0 2 (ι ∷ X4 ∷ []) (zc) ▸
       at 2 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b1 : Chain (ι ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ []) (ι ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ S4⁻ ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ [])
  b1 = at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 1 (CS13⁻ ∷ []) (refl) ▸
       at 13 4 (S4⁻ ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (sym (wl0769 (lit c4))) ▸
       at 15 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 10 4 (S4⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (sym (wl0770 (lit c4))) ▸
       at 8 1 (CS13 ∷ []) (refl) ▸
       at 7 4 (S4⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ []) (sym (wl0771 (lit c4))) ▸
       at 9 1 (Sb0-1-3-2 ∷ []) (refl) ▸ done

  b2 : Chain (ι ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ S4⁻ ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ []) (ι ∷ X4 ∷ Toff014 ∷ X4 ∷ S4⁻ ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ [])
  b2 = at 4 4 (S4⁻ ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (sym (wl0770 (lit c4))) ▸
       at 2 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at243243 c4) ▸
       at 3 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 4 (S4⁻ ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (sym (wp0407 c4)) ▸
       at 7 4 (S4⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (sym (wp0408 c4)) ▸
       at 4 4 (S4⁻ ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (sym (wp0407 c4)) ▸ done

  b3 : Chain (ι ∷ X4 ∷ Toff014 ∷ X4 ∷ S4⁻ ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ [])
  b3 = at 1 4 (S4⁻ ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (sym (wp0408 c4)) ▸
       at 4 2 [] (wl0283 (lit c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸
       at 6 2 [] (wl0283 (lit c4)) ▸
       at 3 4 (Bx0-1423 ∷ []) (sym (lem-beta-T-at243243 c4)) ▸
       at 4 2 [] (wl0283 (lit c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸
       at 6 2 [] (wl0283 (lit c4)) ▸ done

  b4 : Chain (ι ∷ S4⁻ ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ [])
  b4 = at 7 2 [] (wl0283 (lit c4)) ▸
       at 3 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 1 (CS13⁻ ∷ []) (refl) ▸ done

  b5 : Chain (ι ∷ S4⁻ ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ X4 ∷ CS34 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ [])
  b5 = at 14 4 (CS34 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (sym (wl0766 (lit c4))) ▸
       at 16 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 11 4 (CS34 ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (sym (wl0767 (lit c4))) ▸
       at 9 1 (CS13 ∷ []) (refl) ▸
       at 8 4 (CS34 ∷ X4 ∷ CS13 ∷ X4 ∷ []) (sym (wl0768 (lit c4))) ▸
       at 10 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 5 4 (CS34 ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (sym (wl0767 (lit c4))) ▸
       at 3 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at243243 c4) ▸ done

  b6 : Chain (ι ∷ S4⁻ ∷ X4 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ X4 ∷ CS34 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ []) (ι ∷ S4⁻ ∷ CS34 ∷ X4 ∷ Toff014 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ [])
  b6 = at 4 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 4 (CS34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (sym (wp0405 c4)) ▸
       at 8 4 (CS34 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (sym (wp0406 c4)) ▸
       at 5 4 (CS34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (sym (wp0405 c4)) ▸
       at 2 4 (CS34 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (sym (wp0406 c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸ done

  b7 : Chain (ι ∷ S4⁻ ∷ CS34 ∷ X4 ∷ Toff014 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ []) (ι ∷ S4⁻ ∷ CS34 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ [])
  b7 = at 6 2 [] (wl0283 (lit c4)) ▸
       at 7 2 [] (wl0283 (lit c4)) ▸
       at 4 4 (Bx0-1423 ∷ []) (sym (lem-beta-T-at243243 c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸
       at 6 2 [] (wl0283 (lit c4)) ▸
       at 7 2 [] (wl0283 (lit c4)) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸
       at 4 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done

  b8 : Chain (ι ∷ S4⁻ ∷ CS34 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ []) (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS34 ∷ K3 ∷ CS34 ∷ [])
  b8 = at 5 2 (K3 ∷ X4 ∷ []) (sym (wl0732 (lit c4))) ▸
       at 4 2 (K3 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at243243 c4) ▸
       at 3 2 (K3 ∷ X4 ∷ []) (sym (wl0732 (lit c4))) ▸
       at 5 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b9 : Chain (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS34 ∷ K3 ∷ CS34 ∷ []) (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ CS34 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K3 ∷ CS34 ∷ [])
  b9 = at 17 1 (CS13⁻ ∷ []) (refl) ▸
       at 16 4 (CS34 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (sym (wl0766 (lit c4))) ▸
       at 18 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 13 4 (CS34 ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (sym (wl0767 (lit c4))) ▸
       at 11 1 (CS13 ∷ []) (refl) ▸
       at 10 4 (CS34 ∷ X4 ∷ CS13 ∷ X4 ∷ []) (sym (wl0768 (lit c4))) ▸
       at 12 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 7 4 (CS34 ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (sym (wl0767 (lit c4))) ▸ done

  b10 : Chain (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ CS34 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K3 ∷ CS34 ∷ []) (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K3 ∷ CS34 ∷ [])
  b10 = at 5 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at243243 c4) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 13 4 (CS34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (sym (wp0405 c4)) ▸
       at 10 4 (CS34 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (sym (wp0406 c4)) ▸
       at 7 4 (CS34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (sym (wp0405 c4)) ▸
       at 4 4 (CS34 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (sym (wp0406 c4)) ▸ done

  b11 : Chain (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K3 ∷ CS34 ∷ []) (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K3 ∷ CS34 ∷ [])
  b11 = at 7 2 [] (wl0283 (lit c4)) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 6 4 (Bx0-1423 ∷ []) (sym (lem-beta-T-at243243 c4)) ▸
       at 7 2 [] (wl0283 (lit c4)) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸ done

  b12 : Chain (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ K3 ∷ CS34 ∷ []) (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS34 ∷ [])
  b12 = at 6 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 7 2 (K3 ∷ X4 ∷ []) (sym (wl0732 (lit c4))) ▸
       at 6 2 (K3 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at243243 c4) ▸
       at 5 2 (K3 ∷ X4 ∷ []) (sym (wl0732 (lit c4))) ▸
       at 7 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b13 : Chain (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS34 ∷ []) (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ [])
  b13 = at 17 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 19 1 (CS13⁻ ∷ []) (refl) ▸
       at 18 4 (CS34 ∷ X4 ∷ CS13⁻ ∷ X4 ∷ []) (sym (wl0766 (lit c4))) ▸
       at 20 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 15 4 (CS34 ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (sym (wl0767 (lit c4))) ▸
       at 13 1 (CS13 ∷ []) (refl) ▸
       at 12 4 (CS34 ∷ X4 ∷ CS13 ∷ X4 ∷ []) (sym (wl0768 (lit c4))) ▸
       at 14 1 (Sb0-1-3-2 ∷ []) (refl) ▸ done

  b14 : Chain (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ []) (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ X4 ∷ Toff014 ∷ X4 ∷ CS34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ [])
  b14 = at 9 4 (CS34 ∷ X4 ∷ Toff324 ∷ X4 ∷ []) (sym (wl0767 (lit c4))) ▸
       at 7 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at243243 c4) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 4 (CS34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (sym (wp0405 c4)) ▸
       at 12 4 (CS34 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (sym (wp0406 c4)) ▸
       at 9 4 (CS34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ []) (sym (wp0405 c4)) ▸ done

  b15 : Chain (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ X4 ∷ Toff014 ∷ X4 ∷ CS34 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff014 ∷ X4 ∷ X4 ∷ CCZ023 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb0-1-3-2 ∷ X4 ∷ X4 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ []) (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ [])
  b15 = at 6 4 (CS34 ∷ X4 ∷ Toff014 ∷ X4 ∷ []) (sym (wp0406 c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸
       at 11 2 [] (wl0283 (lit c4)) ▸
       at 8 4 (Bx0-1423 ∷ []) (sym (lem-beta-T-at243243 c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸
       at 11 2 [] (wl0283 (lit c4)) ▸ done

  b16 : Chain (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ X4 ∷ X4 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ []) (CK43 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b16 = at 12 2 [] (wl0283 (lit c4)) ▸
       at 8 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 0 7 (CK43 ∷ []) (sym (wl0731 (lit c4))) ▸ done


-- auto CSd01 | BOX(1;2304) @3443: 7 steps
lem-auto-CSd01-∣-BOX⟨1·2304⟩-at3443 : Ws → ⟪ (CS01⁻ ∷ Bx1-2403 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2403 ∷ CS01⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨1·2304⟩-at3443 c4 = run b0
  where
  b0 : Chain (CS01⁻ ∷ Bx1-2403 ∷ []) (Bx1-2403 ∷ CS01⁻ ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (CS01⁻ ∷ Sw34 ∷ []) (sym (c₂ (CS • CS • CS) (Swap ↑))) ▸
       at 2 2 (Bx1-2304 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·2403⟩ (lit c4)) ▸
       at 1 2 (Bx1-2304 ∷ CS01⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨1·2304⟩ c4) ▸
       at 0 2 (Bx1-2403 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·2304⟩ (lit c4)) ▸
       at 1 2 (CS01⁻ ∷ Sw34 ∷ []) (sym (c₂ (CS • CS • CS) (Swap ↑))) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto CSd01 | BOX(1;2304) @12213443: 7 steps
lem-auto-CSd01-∣-BOX⟨1·2304⟩-at12213443 : Ws → ⟪ (CS02⁻ ∷ Bx2-1403 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1403 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨1·2304⟩-at12213443 c4 = run b0
  where
  b0 : Chain (CS02⁻ ∷ Bx2-1403 ∷ []) (Bx2-1403 ∷ CS02⁻ ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CS01⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd02 (lit c4)) ▸
       at 2 2 (Bx1-2403 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·1403⟩ (lit c4)) ▸
       at 1 2 (Bx1-2403 ∷ CS01⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨1·2304⟩-at3443 c4) ▸
       at 0 2 (Bx2-1403 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·2403⟩ (lit c4)) ▸
       at 1 2 (CS02⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd01 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto CSd01 | BOX(1;2304) @0112203443: 7 steps
lem-auto-CSd01-∣-BOX⟨1·2304⟩-at0112203443 : Ws → ⟪ (CS12⁻ ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CS12⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨1·2304⟩-at0112203443 c4 = run b0
  where
  b0 : Chain (CS12⁻ ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CS12⁻ ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CS02⁻ ∷ Sw01 ∷ []) (sym (wl0036 (lit c4))) ▸
       at 2 2 (Bx2-1403 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·0413⟩ (lit c4)) ▸
       at 1 2 (Bx2-1403 ∷ CS02⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨1·2304⟩-at12213443 c4) ▸
       at 0 2 (Bx2-0413 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1403⟩ (lit c4)) ▸
       at 1 2 (CS12⁻ ∷ Sw01 ∷ []) (sym (wl0139 (lit c4))) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(2;0413): 3 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0413⟩ : Ws → ⟪ (Sb⁻0-1-2-3 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ Sb⁻0-1-2-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0413⟩ c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-2-3 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ Sb⁻0-1-2-3 ∷ [])
  b0 = at 0 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 2 (Bx2-0413 ∷ CS12⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨1·2304⟩-at0112203443 c4) ▸
       at 1 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸ done


-- auto CS01 | BOX(1;2304) @3443: 7 steps
lem-auto-CS01-∣-BOX⟨1·2304⟩-at3443 : Ws → ⟪ (CS01 ∷ Bx1-2403 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2403 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨1·2304⟩-at3443 c4 = run b0
  where
  b0 : Chain (CS01 ∷ Bx1-2403 ∷ []) (Bx1-2403 ∷ CS01 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 2 2 (Bx1-2304 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·2403⟩ (lit c4)) ▸
       at 1 2 (Bx1-2304 ∷ CS01 ∷ []) (lem-auto-CS01-∣-BOX⟨1·2304⟩ c4) ▸
       at 0 2 (Bx1-2403 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·2304⟩ (lit c4)) ▸
       at 1 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto CS01 | BOX(1;2304) @12213443: 7 steps
lem-auto-CS01-∣-BOX⟨1·2304⟩-at12213443 : Ws → ⟪ (CS02 ∷ Bx2-1403 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1403 ∷ CS02 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨1·2304⟩-at12213443 c4 = run b0
  where
  b0 : Chain (CS02 ∷ Bx2-1403 ∷ []) (Bx2-1403 ∷ CS02 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CS01 ∷ Sw12 ∷ []) (lem-nat-1-CS02 (lit c4)) ▸
       at 2 2 (Bx1-2403 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·1403⟩ (lit c4)) ▸
       at 1 2 (Bx1-2403 ∷ CS01 ∷ []) (lem-auto-CS01-∣-BOX⟨1·2304⟩-at3443 c4) ▸
       at 0 2 (Bx2-1403 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·2403⟩ (lit c4)) ▸
       at 1 2 (CS02 ∷ Sw12 ∷ []) (lem-nat-1-CS01 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto CS01 | BOX(1;2304) @0112203443: 7 steps
lem-auto-CS01-∣-BOX⟨1·2304⟩-at0112203443 : Ws → ⟪ (CS12 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CS12 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨1·2304⟩-at0112203443 c4 = run b0
  where
  b0 : Chain (CS12 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CS12 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CS02 ∷ Sw01 ∷ []) (sym (wl0035 (lit c4))) ▸
       at 2 2 (Bx2-1403 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·0413⟩ (lit c4)) ▸
       at 1 2 (Bx2-1403 ∷ CS02 ∷ []) (lem-auto-CS01-∣-BOX⟨1·2304⟩-at12213443 c4) ▸
       at 0 2 (Bx2-0413 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1403⟩ (lit c4)) ▸
       at 1 2 (CS12 ∷ Sw01 ∷ []) (sym (wl0138 (lit c4))) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto SBOX(0;1;2;3) | BOX(2;0413): 3 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0413⟩ : Ws → ⟪ (Sb0-1-2-3 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ Sb0-1-2-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0413⟩ c4 = run b0
  where
  b0 : Chain (Sb0-1-2-3 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ Sb0-1-2-3 ∷ [])
  b0 = at 0 1 (CS12 ∷ []) (refl) ▸
       at 0 2 (Bx2-0413 ∷ CS12 ∷ []) (lem-auto-CS01-∣-BOX⟨1·2304⟩-at0112203443 c4) ▸
       at 1 1 (Sb0-1-2-3 ∷ []) (refl) ▸ done


-- beta-T @0412213043: 8 steps
lem-beta-T-at0412213043 : Ws → ⟪ (Bx4-2103 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ []) ⟫ʷ
lem-beta-T-at0412213043 c4 = run b0
  where
  b0 : Chain (Bx4-2103 ∷ []) (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx4-2013 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·2103⟩ (lit c4)) ▸
       at 1 1 (Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ134 ∷ []) (lem-beta-T-at0412203143 c4) ▸
       at 0 2 (Toff412 ∷ Sw01 ∷ []) (lem-nat-0-TOFF402 (lit c4)) ▸
       at 1 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 (lit c4)) ▸
       at 2 2 (Toff412 ∷ Sw01 ∷ []) (lem-nat-0-TOFF402 (lit c4)) ▸
       at 3 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 (lit c4)) ▸
       at 4 2 [] (wl0002 (lit c4)) ▸ done


-- sym23 @0412213043: 5 steps
lem-sym23-at0412213043 : Ws → ⟪ (Bx4-2103 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2013 ∷ []) ⟫ʷ
lem-sym23-at0412213043 c4 = run b0
  where
  b0 : Chain (Bx4-2103 ∷ []) (Bx4-2013 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx4-2013 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·2103⟩ (lit c4)) ▸
       at 1 1 (Bx4-2103 ∷ []) (lem-sym23-at0412203143 c4) ▸
       at 0 2 (Bx4-2013 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·2103⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- auto BOX(0;1234) | BOX(4;0213): 27 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨4·0213⟩ : Ws → ⟪ (Bx0-1234 ∷ Bx4-0213 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0213 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨4·0213⟩ c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Bx0-1234 ∷ Bx4-0213 ∷ []) (Toff412 ∷ Bx0-1243 ∷ CCZ123 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ [])
  b0 = at 1 1 (Bx4-2013 ∷ []) (lem-sym12-at04103143 c4) ▸
       at 1 1 (Bx4-2103 ∷ []) (lem-sym23-at0412203143 c4) ▸
       at 1 1 (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ []) (lem-beta-T-at0412213043 c4) ▸
       at 0 0 (Toff412 ∷ Toff412 ∷ []) (sym (wl0784 (lit c4))) ▸
       at 1 1 (Toff412 ∷ []) (wl0785 (lit c4)) ▸
       at 3 1 (Toff412 ∷ []) (wl0785 (lit c4)) ▸
       at 2 1 (Bx0-1243 ∷ []) (lem-sym34 c4) ▸
       at 1 3 (Bx0-1243 ∷ CCZ123 ∷ []) (lem-T312-beta-at3443 c4) ▸ done

  b1 : Chain (Toff412 ∷ Bx0-1243 ∷ CCZ123 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ []) (Toff412 ∷ CCZ123 ∷ CCZ034 ∷ Toff412 ∷ Bx0-1243 ∷ CCZ123 ∷ CCZ034 ∷ [])
  b1 = at 1 1 (Bx0-1234 ∷ []) (lem-sym34-at3443 c4) ▸
       at 1 2 (CCZ123 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ123 c4) ▸
       at 2 2 (CCZ034 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ403 c4) ▸
       at 3 0 (Toff412 ∷ Toff412 ∷ []) (sym (wl0784 (lit c4))) ▸
       at 4 1 (Toff412 ∷ []) (wl0785 (lit c4)) ▸
       at 6 1 (Toff412 ∷ []) (wl0785 (lit c4)) ▸
       at 5 1 (Bx0-1243 ∷ []) (lem-sym34 c4) ▸
       at 4 3 (Bx0-1243 ∷ CCZ123 ∷ []) (lem-T312-beta-at3443 c4) ▸ done

  b2 : Chain (Toff412 ∷ CCZ123 ∷ CCZ034 ∷ Toff412 ∷ Bx0-1243 ∷ CCZ123 ∷ CCZ034 ∷ []) (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ Bx0-1234 ∷ [])
  b2 = at 4 1 (Bx0-1234 ∷ []) (lem-sym34-at3443 c4) ▸
       at 4 2 (CCZ123 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ123 c4) ▸
       at 5 2 (CCZ034 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ403 c4) ▸
       at 0 2 (CCZ123 ∷ Toff412 ∷ []) (sym (wl0786 (lit c4))) ▸
       at 3 2 (CCZ123 ∷ Toff412 ∷ []) (sym (wl0786 (lit c4))) ▸
       at 2 2 (CCZ123 ∷ CCZ034 ∷ []) (lem-auto-CCZ012-∣-CCZ342-at0410233142 c4) ▸
       at 1 2 (CCZ123 ∷ Toff412 ∷ []) (sym (wl0786 (lit c4))) ▸
       at 0 2 [] (wl0212 (lit c4)) ▸ done

  b3 : Chain (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ Bx0-1234 ∷ []) (Bx4-0213 ∷ Bx0-1234 ∷ [])
  b3 = at 0 4 (Bx4-2103 ∷ []) (sym (lem-beta-T-at0412213043 c4)) ▸
       at 0 1 (Bx4-2013 ∷ []) (lem-sym23-at0412213043 c4) ▸
       at 0 1 (Bx4-0213 ∷ []) (lem-sym12-at0412203143 c4) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(2;0413) @2332: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0413⟩-at2332 : Ws → ⟪ (Sb⁻0-1-3-2 ∷ Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ Sb⁻0-1-3-2 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0413⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-3-2 ∷ Bx3-0412 ∷ []) (Bx3-0412 ∷ Sb⁻0-1-3-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb⁻0-1-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·3·2⟩ (lit c4)) ▸
       at 2 2 (Bx2-0413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0412⟩ (lit c4)) ▸
       at 1 2 (Bx2-0413 ∷ Sb⁻0-1-2-3 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0413⟩ c4) ▸
       at 0 2 (Bx3-0412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0413⟩ (lit c4)) ▸
       at 1 2 (Sb⁻0-1-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·2·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(2;0413) @243243: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0413⟩-at243243 : Ws → ⟪ (Sb⁻0-1-4-2 ∷ Bx4-0312 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0312 ∷ Sb⁻0-1-4-2 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0413⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-4-2 ∷ Bx4-0312 ∷ []) (Bx4-0312 ∷ Sb⁻0-1-4-2 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Sb⁻0-1-3-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·4·2⟩ (lit c4)) ▸
       at 2 2 (Bx3-0412 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·0312⟩ (lit c4)) ▸
       at 1 2 (Bx3-0412 ∷ Sb⁻0-1-3-2 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0413⟩-at2332 c4) ▸
       at 0 2 (Bx4-0312 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·0412⟩ (lit c4)) ▸
       at 1 2 (Sb⁻0-1-4-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·3·2⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(2;0413) @2442: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0413⟩-at2442 : Ws → ⟪ (Sb⁻0-1-4-3 ∷ Bx4-0213 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0213 ∷ Sb⁻0-1-4-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0413⟩-at2442 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-4-3 ∷ Bx4-0213 ∷ []) (Bx4-0213 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb⁻0-1-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·4·3⟩ (lit c4)) ▸
       at 2 2 (Bx4-0312 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0213⟩ (lit c4)) ▸
       at 1 2 (Bx4-0312 ∷ Sb⁻0-1-4-2 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0413⟩-at243243 c4) ▸
       at 0 2 (Bx4-0213 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0312⟩ (lit c4)) ▸
       at 1 2 (Sb⁻0-1-4-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·4·2⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOX(0;1;2;3) | BOX(2;0413) @2332: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0413⟩-at2332 : Ws → ⟪ (Sb0-1-3-2 ∷ Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ Sb0-1-3-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0413⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-3-2 ∷ Bx3-0412 ∷ []) (Bx3-0412 ∷ Sb0-1-3-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·3·2⟩ (lit c4)) ▸
       at 2 2 (Bx2-0413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0412⟩ (lit c4)) ▸
       at 1 2 (Bx2-0413 ∷ Sb0-1-2-3 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0413⟩ c4) ▸
       at 0 2 (Bx3-0412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0413⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·2·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOX(0;1;2;3) | BOX(2;0413) @243243: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0413⟩-at243243 : Ws → ⟪ (Sb0-1-4-2 ∷ Bx4-0312 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0312 ∷ Sb0-1-4-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0413⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-4-2 ∷ Bx4-0312 ∷ []) (Bx4-0312 ∷ Sb0-1-4-2 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Sb0-1-3-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·4·2⟩ (lit c4)) ▸
       at 2 2 (Bx3-0412 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·0312⟩ (lit c4)) ▸
       at 1 2 (Bx3-0412 ∷ Sb0-1-3-2 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0413⟩-at2332 c4) ▸
       at 0 2 (Bx4-0312 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·0412⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-4-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·3·2⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto SBOX(0;1;2;3) | BOX(2;0413) @2442: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0413⟩-at2442 : Ws → ⟪ (Sb0-1-4-3 ∷ Bx4-0213 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0213 ∷ Sb0-1-4-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0413⟩-at2442 c4 = run b0
  where
  b0 : Chain (Sb0-1-4-3 ∷ Bx4-0213 ∷ []) (Bx4-0213 ∷ Sb0-1-4-3 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·4·3⟩ (lit c4)) ▸
       at 2 2 (Bx4-0312 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0213⟩ (lit c4)) ▸
       at 1 2 (Bx4-0312 ∷ Sb0-1-4-2 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0413⟩-at243243 c4) ▸
       at 0 2 (Bx4-0213 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0312⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-4-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·4·2⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | BOX(4;0213): 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·0213⟩ : Ws → ⟪ (Sb0-1-23-4 ∷ Bx4-0213 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0213 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·0213⟩ c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ Bx4-0213 ∷ []) (Bx4-0213 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 2 (Bx4-0213 ∷ Sb⁻0-1-4-3 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨2·0413⟩-at2442 c4) ▸
       at 3 2 (Bx4-0213 ∷ Toff423 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at0412233041 c4) ▸
       at 2 2 (Bx4-0213 ∷ Sb0-1-4-3 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨2·0413⟩-at2442 c4) ▸
       at 1 2 (Bx4-0213 ∷ Toff423 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·3142⟩-at0412233041 c4) ▸
       at 0 2 (Bx4-0213 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨4·0213⟩ c4) ▸
       at 1 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- auto CCZ012 | BOX(0;1324): 3 steps
lem-auto-CCZ012-∣-BOX⟨0·1324⟩ : Ws → ⟪ (CCZ012 ∷ Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨0·1324⟩ c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Bx0-1324 ∷ []) (Bx0-1324 ∷ CCZ012 ∷ [])
  b0 = at 1 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸
       at 0 2 (Bx0-1234 ∷ CCZ012 ∷ []) (lem-Cz-beta c4) ▸
       at 0 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸ done


-- auto CCZ012 | SBOX(0;1;32;4): 11 steps
lem-auto-CCZ012-∣-SBOX⟨0·1·32·4⟩ : Ws → ⟪ (CCZ012 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-32-4 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨0·1·32·4⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ012 ∷ Sb0-1-32-4 ∷ []) (Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ CCZ012 ∷ CS14⁻ ∷ [])
  b0 = at 1 1 (Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ []) (refl) ▸
       at 0 2 (Bx0-1324 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-BOX⟨0·1324⟩ c4) ▸
       at 1 2 (Toff423 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-TOFF342-at3443 c4) ▸
       at 3 1 (CS14 ∷ []) (refl) ▸
       at 2 2 (CS14 ∷ CCZ012 ∷ []) (wp0044 c4) ▸
       at 2 1 (Sb0-1-4-2 ∷ []) (refl) ▸
       at 3 2 (Toff423 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-TOFF342-at3443 c4) ▸
       at 5 1 (CS14⁻ ∷ []) (refl) ▸ done

  b1 : Chain (Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ CCZ012 ∷ CS14⁻ ∷ []) (Sb0-1-32-4 ∷ CCZ012 ∷ [])
  b1 = at 4 2 (CS14⁻ ∷ CCZ012 ∷ []) (wp0043 c4) ▸
       at 4 1 (Sb⁻0-1-4-2 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-32-4 ∷ []) (refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOX(4;0;3;1): 5 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨4·0·3·1⟩ : Ws → ⟪ (Sb0-1-23-4 ∷ Sb4-0-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-0-3-1 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨4·0·3·1⟩ c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ Sb4-0-3-1 ∷ []) (Sb4-0-3-1 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 1 1 (CS03 ∷ []) (refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS03 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS02-at2332 c4) ▸
       at 1 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 1 (Sb4-0-3-1 ∷ []) (refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOXd(4;0;3;1): 5 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·0·3·1⟩ : Ws → ⟪ (Sb0-1-23-4 ∷ Sb⁻4-0-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-0-3-1 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·0·3·1⟩ c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ Sb⁻4-0-3-1 ∷ []) (Sb⁻4-0-3-1 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 1 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS03⁻ ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd02-at2332 c4) ▸
       at 1 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 1 (Sb⁻4-0-3-1 ∷ []) (refl) ▸ done


-- auto SBOX(0;1;23;4) | BOX(4;0213) @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·0213⟩-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ Bx4-0312 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0312 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·0213⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ Bx4-0312 ∷ []) (Bx4-0312 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 (Bx4-0213 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0312⟩ (lit c4)) ▸
       at 1 2 (Bx4-0213 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·0213⟩ c4) ▸
       at 0 2 (Bx4-0312 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0213⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | BOX(4;0213) @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·0213⟩-at243243 : Ws → ⟪ (Sb0-1-42-3 ∷ Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·0213⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ Bx3-0412 ∷ []) (Bx3-0412 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 (Bx4-0312 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·0412⟩ (lit c4)) ▸
       at 1 2 (Bx4-0312 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨4·0213⟩-at2332 c4) ▸
       at 0 2 (Bx3-0412 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·0312⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto CCZ012 | SBOX(0;1;32;4) @3443: 7 steps
lem-auto-CCZ012-∣-SBOX⟨0·1·32·4⟩-at3443 : Ws → ⟪ (CCZ012 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨0·1·32·4⟩-at3443 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ CCZ012 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 2 2 (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-32-4 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨0·1·32·4⟩ c4) ▸
       at 0 2 (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 1 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | SBOX(4;0;3;1) @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨4·0·3·1⟩-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ Sb4-0-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-0-2-1 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨4·0·3·1⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ Sb4-0-2-1 ∷ []) (Sb4-0-2-1 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 (Sb4-0-3-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨4·0·2·1⟩ (lit c4)) ▸
       at 1 2 (Sb4-0-3-1 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨4·0·3·1⟩ c4) ▸
       at 0 2 (Sb4-0-2-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨4·0·3·1⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | SBOX(4;0;3;1) @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨4·0·3·1⟩-at243243 : Ws → ⟪ (Sb0-1-42-3 ∷ Sb3-0-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-2-1 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨4·0·3·1⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ Sb3-0-2-1 ∷ []) (Sb3-0-2-1 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 (Sb4-0-2-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨3·0·2·1⟩ (lit c4)) ▸
       at 1 2 (Sb4-0-2-1 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨4·0·3·1⟩-at2332 c4) ▸
       at 0 2 (Sb3-0-2-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨4·0·2·1⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | SBOXd(4;0;3;1) @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·0·3·1⟩-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ Sb⁻4-0-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-0-2-1 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·0·3·1⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ Sb⁻4-0-2-1 ∷ []) (Sb⁻4-0-2-1 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 (Sb⁻4-0-3-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨4·0·2·1⟩ (lit c4)) ▸
       at 1 2 (Sb⁻4-0-3-1 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·0·3·1⟩ c4) ▸
       at 0 2 (Sb⁻4-0-2-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨4·0·3·1⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | SBOXd(4;0;3;1) @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·0·3·1⟩-at243243 : Ws → ⟪ (Sb0-1-42-3 ∷ Sb⁻3-0-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-0-2-1 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·0·3·1⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ Sb⁻3-0-2-1 ∷ []) (Sb⁻3-0-2-1 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 (Sb⁻4-0-2-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨3·0·2·1⟩ (lit c4)) ▸
       at 1 2 (Sb⁻4-0-2-1 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨4·0·3·1⟩-at2332 c4) ▸
       at 0 2 (Sb⁻3-0-2-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨4·0·2·1⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


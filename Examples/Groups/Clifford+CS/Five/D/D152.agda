{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D152 where

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
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-CSd12-beta ; lem-CX23-beta ; lem-sym23)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-c124-beta-at2332 ; lem-sym23-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-CSd12-beta-at2332 ; lem-CX23-beta-at243243 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CS21-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D007 using (lem-SBsym-at0113203442)
open import Examples.Groups.Clifford+CS.Five.D.D008 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS31-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D010 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS01)
open import Examples.Groups.Clifford+CS.Five.D.D135 using (lem-CX23-beta-at0410213243 ; lem-CX23-beta-at04203243 ; lem-F0-at0112203443 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ142-at04233240 ; lem-sym23-at04102142 ; lem-sym23-at0410233142 ; lem-sym23-at04203243 ; lem-sym23-at04233240 ; lem-sym23-at043043 ; lem-sym23-at0440 ; lem-sym34-at04103143 ; lem-sym34-at043043 ; lem-sym34-at0440)
open import Examples.Groups.Clifford+CS.Five.D.D151 using (lem-F0-at0314213042 ; lem-auto-CK01-∣-BOX⟨1·2034⟩ ; lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at04203243)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-CCZ023 ; lem-nat-1-CCZ034 ; lem-nat-2-BOX⟨0·1234⟩ ; lem-nat-2-BOX⟨0·1324⟩ ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ013 ; lem-nat-2-CCZ024 ; lem-nat-2-CCZ034 ; lem-nat-3-CCZ024)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-1-CCZ013 ; lem-nat-3-CCZ023)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-2-CCZ134)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-0-CCZ034 ; lem-nat-0-CCZ134)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-0-BOX⟨0·1234⟩ ; lem-nat-0-BOX⟨1·0234⟩ ; lem-nat-1-BOX⟨1·0234⟩ ; lem-nat-1-BOX⟨2·0134⟩ ; lem-nat-2-BOX⟨2·0134⟩ ; lem-nat-2-BOX⟨3·0124⟩)
open import Examples.Groups.Clifford+CS.Five.D.R013 using (lem-nat-2-CSd12 ; lem-nat-2-CSd13)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-0-SBOX⟨0·1·42·3⟩ ; lem-nat-0-SBOX⟨1·0·42·3⟩ ; lem-nat-1-CSd02 ; lem-nat-1-SBOX⟨1·0·42·3⟩ ; lem-nat-1-SBOX⟨2·0·41·3⟩ ; lem-nat-2-BOX⟨0·1432⟩ ; lem-nat-2-CSd02 ; lem-nat-2-SBOX⟨0·1·23·4⟩ ; lem-nat-2-SBOX⟨0·1·32·4⟩)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-1-CSd01)
open import Examples.Groups.Clifford+CS.Five.D.R016 using (lem-nat-1-BOX⟨4·0312⟩)
open import Examples.Groups.Clifford+CS.Five.D.R017 using (lem-nat-2-BOX⟨4·0123⟩ ; lem-nat-2-BOX⟨4·0132⟩ ; lem-nat-3-BOX⟨3·0124⟩ ; lem-nat-3-BOX⟨4·0123⟩)
open import Examples.Groups.Clifford+CS.Five.D.R019 using (lem-nat-2-BOX⟨0·1423⟩ ; lem-nat-2-CSd03)
open import Examples.Groups.Clifford+CS.Five.D.R020 using (lem-nat-2-SBOX⟨0·1·42·3⟩ ; lem-nat-2-SBOX⟨0·1·43·2⟩ ; lem-nat-3-SBOX⟨1·2·34·0⟩ ; lem-nat-3-SBOX⟨1·2·43·0⟩)
open import Examples.Groups.Clifford+CS.Five.D.R021 using (lem-nat-0-SBOX⟨0·2·43·1⟩ ; lem-nat-0-SBOX⟨1·2·43·0⟩ ; lem-nat-0-SBOX⟨2·3·04·1⟩ ; lem-nat-0-SBOX⟨2·3·14·0⟩ ; lem-nat-1-SBOX⟨0·1·43·2⟩ ; lem-nat-1-SBOX⟨0·2·43·1⟩ ; lem-nat-1-SBOX⟨1·3·24·0⟩ ; lem-nat-1-SBOX⟨2·3·14·0⟩ ; lem-nat-2-SBOX⟨1·2·34·0⟩ ; lem-nat-2-SBOX⟨1·3·24·0⟩)
open import Examples.Groups.Clifford+CS.Five.D.R029 using (lem-nat-0-BOX⟨4·0321⟩ ; lem-nat-0-BOX⟨4·1320⟩ ; lem-nat-1-BOX⟨4·0213⟩ ; lem-nat-1-BOX⟨4·0321⟩ ; lem-nat-2-BOX⟨4·0312⟩)
open import Examples.Groups.Clifford+CS.Five.D.R030 using (lem-nat-0-BOX⟨4·0132⟩ ; lem-nat-0-BOX⟨4·1302⟩ ; lem-nat-1-BOX⟨4·0123⟩ ; lem-nat-2-BOX⟨4·0213⟩)
open import Examples.Groups.Clifford+CS.Five.D.R033 using (lem-nat-0-SBOX⟨0·1·43·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R034 using (lem-nat-0-BOX⟨4·0312⟩ ; lem-nat-0-BOX⟨4·1032⟩ ; lem-nat-0-CK40 ; lem-nat-0-CK41 ; lem-nat-0-SBOX⟨0·3·14·2⟩ ; lem-nat-0-SBOX⟨1·0·43·2⟩ ; lem-nat-1-CK10 ; lem-nat-1-CK20 ; lem-nat-1-SBOX⟨0·3·24·1⟩ ; lem-nat-2-BOX⟨1·2043⟩ ; lem-nat-2-BOX⟨1·3042⟩ ; lem-nat-2-BOX⟨4·0231⟩ ; lem-nat-2-CK20 ; lem-nat-2-CK30 ; lem-nat-2-CX13 ; lem-nat-3-BOX⟨1·2034⟩ ; lem-nat-3-BOX⟨1·2043⟩ ; lem-nat-3-CK30 ; lem-nat-3-CK40)
-- F0 @03143041: 5 steps
lem-F0-at03143041 : Complete 4 → ⟪ (Sb2-3-14-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-3-14-2 ∷ []) ⟫ʷ
lem-F0-at03143041 c4 = run b0
  where
  b0 : Chain (Sb2-3-14-0 ∷ []) (Sb0-3-14-2 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb1-3-24-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·3·14·0⟩ c4) ▸
       at 1 1 (Sb0-3-24-1 ∷ []) (lem-F0-at0314213042 c4) ▸
       at 0 2 (Sb0-3-14-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·3·24·1⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- F0 @03143140: 5 steps
lem-F0-at03143140 : Complete 4 → ⟪ (Sb2-3-04-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-3-04-2 ∷ []) ⟫ʷ
lem-F0-at03143140 c4 = run b0
  where
  b0 : Chain (Sb2-3-04-1 ∷ []) (Sb1-3-04-2 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb2-3-14-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·3·04·1⟩ c4) ▸
       at 1 1 (Sb0-3-14-2 ∷ []) (lem-F0-at03143041 c4) ▸
       at 0 2 (Sb1-3-04-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·3·14·2⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CK01 | BOX(1;2034) @3443: 7 steps
lem-auto-CK01-∣-BOX⟨1·2034⟩-at3443 : Complete 4 → ⟪ (CK01 ∷ Bx1-2043 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2043 ∷ CK01 ∷ []) ⟫ʷ
lem-auto-CK01-∣-BOX⟨1·2034⟩-at3443 c4 = run b0
  where
  b0 : Chain (CK01 ∷ Bx1-2043 ∷ []) (Bx1-2043 ∷ CK01 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CK01 ∷ Sw34 ∷ []) (sym (c₂ (CK₀₁) (Swap ↑))) ▸
       at 2 2 (Bx1-2034 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·2043⟩ c4) ▸
       at 1 2 (Bx1-2034 ∷ CK01 ∷ []) (lem-auto-CK01-∣-BOX⟨1·2034⟩ c4) ▸
       at 0 2 (Bx1-2043 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·2034⟩ c4) ▸
       at 1 2 (CK01 ∷ Sw34 ∷ []) (sym (c₂ (CK₀₁) (Swap ↑))) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CK01 | BOX(1;2034) @233442: 7 steps
lem-auto-CK01-∣-BOX⟨1·2034⟩-at233442 : Complete 4 → ⟪ (CK01 ∷ Bx1-3042 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3042 ∷ CK01 ∷ []) ⟫ʷ
lem-auto-CK01-∣-BOX⟨1·2034⟩-at233442 c4 = run b0
  where
  b0 : Chain (CK01 ∷ Bx1-3042 ∷ []) (Bx1-3042 ∷ CK01 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CK01 ∷ Sw23 ∷ []) (sym (c₂ (CK₀₁) (Swap))) ▸
       at 2 2 (Bx1-2043 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·3042⟩ c4) ▸
       at 1 2 (Bx1-2043 ∷ CK01 ∷ []) (lem-auto-CK01-∣-BOX⟨1·2034⟩-at3443 c4) ▸
       at 0 2 (Bx1-3042 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·2043⟩ c4) ▸
       at 1 2 (CK01 ∷ Sw23 ∷ []) (sym (c₂ (CK₀₁) (Swap))) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CK01 | SBOX(2;3;04;1): 13 steps
lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩ : Complete 4 → ⟪ (CK01 ∷ Sb2-3-04-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-04-1 ∷ CK01 ∷ []) ⟫ʷ
lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CK01 ∷ Sb2-3-04-1 ∷ []) (Bx1-3042 ∷ Toff204 ∷ Sb1-3-2-4 ∷ Toff204 ∷ CK01 ∷ Sb⁻1-3-2-4 ∷ [])
  b0 = at 1 1 (Sb1-3-04-2 ∷ []) (lem-F0-at03143140 c4) ▸
       at 1 1 (Bx1-3042 ∷ Toff204 ∷ Sb1-3-2-4 ∷ Toff204 ∷ Sb⁻1-3-2-4 ∷ []) (refl) ▸
       at 0 2 (Bx1-3042 ∷ CK01 ∷ []) (lem-auto-CK01-∣-BOX⟨1·2034⟩-at233442 c4) ▸
       at 1 2 (Toff204 ∷ CK01 ∷ []) (pw3 c4 (CK01 ∷ Toff204 ∷ []) (Toff204 ∷ CK01 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CS23 ∷ []) (refl) ▸
       at 2 2 (CS23 ∷ CK01 ∷ []) (lw4 c4 (CK01 ∷ CS23 ∷ []) (CS23 ∷ CK01 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb1-3-2-4 ∷ []) (refl) ▸
       at 3 2 (Toff204 ∷ CK01 ∷ []) (pw3 c4 (CK01 ∷ Toff204 ∷ []) (Toff204 ∷ CK01 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Bx1-3042 ∷ Toff204 ∷ Sb1-3-2-4 ∷ Toff204 ∷ CK01 ∷ Sb⁻1-3-2-4 ∷ []) (Sb2-3-04-1 ∷ CK01 ∷ [])
  b1 = at 5 1 (CS23⁻ ∷ []) (refl) ▸
       at 4 2 (CS23⁻ ∷ CK01 ∷ []) (lw4 c4 (CK01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CK01 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻1-3-2-4 ∷ []) (refl) ▸
       at 0 5 (Sb1-3-04-2 ∷ []) (refl) ▸
       at 0 1 (Sb2-3-04-1 ∷ []) (sym (lem-F0-at03143140 c4)) ▸ done


-- auto CK01 | SBOX(2;3;04;1) @0110: 7 steps
lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at0110 : Complete 4 → ⟪ (CK10 ∷ Sb2-3-14-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-14-0 ∷ CK10 ∷ []) ⟫ʷ
lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at0110 c4 = run b0
  where
  b0 : Chain (CK10 ∷ Sb2-3-14-0 ∷ []) (Sb2-3-14-0 ∷ CK10 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CK01 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CK10 ∷ []) (CK01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb2-3-04-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·3·14·0⟩ c4) ▸
       at 1 2 (Sb2-3-04-1 ∷ CK01 ∷ []) (lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩ c4) ▸
       at 0 2 (Sb2-3-14-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·3·04·1⟩ c4) ▸
       at 1 2 (CK10 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CK01 ∷ []) (CK10 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CK01 | SBOX(2;3;04;1) @021021: 7 steps
lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at021021 : Complete 4 → ⟪ (CK20 ∷ Sb1-3-24-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-3-24-0 ∷ CK20 ∷ []) ⟫ʷ
lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at021021 c4 = run b0
  where
  b0 : Chain (CK20 ∷ Sb1-3-24-0 ∷ []) (Sb1-3-24-0 ∷ CK20 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CK10 ∷ Sw12 ∷ []) (lem-nat-1-CK20 c4) ▸
       at 2 2 (Sb2-3-14-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·3·24·0⟩ c4) ▸
       at 1 2 (Sb2-3-14-0 ∷ CK10 ∷ []) (lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at0110 c4) ▸
       at 0 2 (Sb1-3-24-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·3·14·0⟩ c4) ▸
       at 1 2 (CK20 ∷ Sw12 ∷ []) (lem-nat-1-CK10 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CK01 | SBOX(2;3;04;1) @03102132: 7 steps
lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at03102132 : Complete 4 → ⟪ (CK30 ∷ Sb1-2-34-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-34-0 ∷ CK30 ∷ []) ⟫ʷ
lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at03102132 c4 = run b0
  where
  b0 : Chain (CK30 ∷ Sb1-2-34-0 ∷ []) (Sb1-2-34-0 ∷ CK30 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CK20 ∷ Sw23 ∷ []) (lem-nat-2-CK30 c4) ▸
       at 2 2 (Sb1-3-24-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·2·34·0⟩ c4) ▸
       at 1 2 (Sb1-3-24-0 ∷ CK20 ∷ []) (lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at021021 c4) ▸
       at 0 2 (Sb1-2-34-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·3·24·0⟩ c4) ▸
       at 1 2 (CK30 ∷ Sw23 ∷ []) (lem-nat-2-CK20 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CK01 | SBOX(2;3;04;1) @0410213243: 7 steps
lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at0410213243 : Complete 4 → ⟪ (CK40 ∷ Sb1-2-43-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-43-0 ∷ CK40 ∷ []) ⟫ʷ
lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at0410213243 c4 = run b0
  where
  b0 : Chain (CK40 ∷ Sb1-2-43-0 ∷ []) (Sb1-2-43-0 ∷ CK40 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CK30 ∷ Sw34 ∷ []) (lem-nat-3-CK40 c4) ▸
       at 2 2 (Sb1-2-34-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·2·43·0⟩ c4) ▸
       at 1 2 (Sb1-2-34-0 ∷ CK30 ∷ []) (lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at03102132 c4) ▸
       at 0 2 (Sb1-2-43-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·2·34·0⟩ c4) ▸
       at 1 2 (CK40 ∷ Sw34 ∷ []) (lem-nat-3-CK30 c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CK01 | SBOX(2;3;04;1) @04203243: 7 steps
lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at04203243 : Complete 4 → ⟪ (CK41 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ CK41 ∷ []) ⟫ʷ
lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at04203243 c4 = run b0
  where
  b0 : Chain (CK41 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ CK41 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CK40 ∷ Sw01 ∷ []) (lem-nat-0-CK41 c4) ▸
       at 2 2 (Sb1-2-43-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·2·43·1⟩ c4) ▸
       at 1 2 (Sb1-2-43-0 ∷ CK40 ∷ []) (lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at0410213243 c4) ▸
       at 0 2 (Sb0-2-43-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·2·43·0⟩ c4) ▸
       at 1 2 (CK41 ∷ Sw01 ∷ []) (lem-nat-0-CK40 c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- F2 K1|CS23: 1 steps
lem-F2-K1∣CS23 : Complete 4 → ⟪ (CK41 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ CK41 ∷ []) ⟫ʷ
lem-F2-K1∣CS23 c4 = run b0
  where
  b0 : Chain (CK41 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ CK41 ∷ [])
  b0 = at 0 2 (Sb0-2-43-1 ∷ CK41 ∷ []) (lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at04203243 c4) ▸ done


-- auto CK01 | SBOX(1;2;03;4) @0412203143: 7 steps
lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at0412203143 : Complete 4 → ⟪ (CK42 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CK42 ∷ []) ⟫ʷ
lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at0412203143 c4 = run b0
  where
  b0 : Chain (CK42 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CK42 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CK41 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CK42 ∷ []) (CK41 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ c4) ▸
       at 1 2 (Sb1-0-42-3 ∷ CK41 ∷ []) (lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at04203243 c4) ▸
       at 0 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ c4) ▸
       at 1 2 (CK42 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CK41 ∷ []) (CK42 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- F2 K2|CS01: 1 steps
lem-F2-K2∣CS01 : Complete 4 → ⟪ (CK42 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CK42 ∷ []) ⟫ʷ
lem-F2-K2∣CS01 c4 = run b0
  where
  b0 : Chain (CK42 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CK42 ∷ [])
  b0 = at 0 2 (Sb2-0-41-3 ∷ CK42 ∷ []) (lem-auto-CK01-∣-SBOX⟨1·2·03·4⟩-at0412203143 c4) ▸ done


-- auto CK01 | SBOX(2;3;04;1) @0412203143: 7 steps
lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at0412203143 : Complete 4 → ⟪ (CK42 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-43-2 ∷ CK42 ∷ []) ⟫ʷ
lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at0412203143 c4 = run b0
  where
  b0 : Chain (CK42 ∷ Sb0-1-43-2 ∷ []) (Sb0-1-43-2 ∷ CK42 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CK41 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CK42 ∷ []) (CK41 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ c4) ▸
       at 1 2 (Sb0-2-43-1 ∷ CK41 ∷ []) (lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at04203243 c4) ▸
       at 0 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ c4) ▸
       at 1 2 (CK42 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CK41 ∷ []) (CK42 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CK01 | SBOX(2;3;04;1) @0412213043: 7 steps
lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at0412213043 : Complete 4 → ⟪ (CK42 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-43-2 ∷ CK42 ∷ []) ⟫ʷ
lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at0412213043 c4 = run b0
  where
  b0 : Chain (CK42 ∷ Sb1-0-43-2 ∷ []) (Sb1-0-43-2 ∷ CK42 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸
       at 2 2 (Sb0-1-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·43·2⟩ c4) ▸
       at 1 2 (Sb0-1-43-2 ∷ CK42 ∷ []) (lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at0412203143 c4) ▸
       at 0 2 (Sb1-0-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·43·2⟩ c4) ▸
       at 1 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- F2 K2|CS03: 1 steps
lem-F2-K2∣CS03 : Complete 4 → ⟪ (CK42 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-43-2 ∷ CK42 ∷ []) ⟫ʷ
lem-F2-K2∣CS03 c4 = run b0
  where
  b0 : Chain (CK42 ∷ Sb1-0-43-2 ∷ []) (Sb1-0-43-2 ∷ CK42 ∷ [])
  b0 = at 0 2 (Sb1-0-43-2 ∷ CK42 ∷ []) (lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at0412213043 c4) ▸ done


-- F2 K2|CS13: 1 steps
lem-F2-K2∣CS13 : Complete 4 → ⟪ (CK42 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-43-2 ∷ CK42 ∷ []) ⟫ʷ
lem-F2-K2∣CS13 c4 = run b0
  where
  b0 : Chain (CK42 ∷ Sb0-1-43-2 ∷ []) (Sb0-1-43-2 ∷ CK42 ∷ [])
  b0 = at 0 2 (Sb0-1-43-2 ∷ CK42 ∷ []) (lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at0412203143 c4) ▸ done


-- auto CK01 | SBOX(2;3;04;1) @0413203142: 7 steps
lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at0413203142 : Complete 4 → ⟪ (CK43 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CK43 ∷ []) ⟫ʷ
lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at0413203142 c4 = run b0
  where
  b0 : Chain (CK43 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ CK43 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CK42 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CK43 ∷ []) (CK42 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ c4) ▸
       at 1 2 (Sb0-1-43-2 ∷ CK42 ∷ []) (lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at0412203143 c4) ▸
       at 0 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ c4) ▸
       at 1 2 (CK43 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CK42 ∷ []) (CK43 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CK01 | SBOX(2;3;04;1) @0413213042: 7 steps
lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at0413213042 : Complete 4 → ⟪ (CK43 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ CK43 ∷ []) ⟫ʷ
lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at0413213042 c4 = run b0
  where
  b0 : Chain (CK43 ∷ Sb1-0-42-3 ∷ []) (Sb1-0-42-3 ∷ CK43 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CK43 ∷ Sw01 ∷ []) (c₂ (Swap) (CK₁₀ ↑)) ▸
       at 2 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ c4) ▸
       at 1 2 (Sb0-1-42-3 ∷ CK43 ∷ []) (lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at0413203142 c4) ▸
       at 0 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ c4) ▸
       at 1 2 (CK43 ∷ Sw01 ∷ []) (c₂ (Swap) (CK₁₀ ↑)) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CK01 | SBOX(2;3;04;1) @04133041: 7 steps
lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at04133041 : Complete 4 → ⟪ (CK43 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CK43 ∷ []) ⟫ʷ
lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at04133041 c4 = run b0
  where
  b0 : Chain (CK43 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CK43 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CK43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CK₁₀)) ▸
       at 2 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ c4) ▸
       at 1 2 (Sb1-0-42-3 ∷ CK43 ∷ []) (lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at0413213042 c4) ▸
       at 0 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ c4) ▸
       at 1 2 (CK43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CK₁₀)) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- F2 K3|CS01: 1 steps
lem-F2-K3∣CS01 : Complete 4 → ⟪ (CK43 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CK43 ∷ []) ⟫ʷ
lem-F2-K3∣CS01 c4 = run b0
  where
  b0 : Chain (CK43 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CK43 ∷ [])
  b0 = at 0 2 (Sb2-0-41-3 ∷ CK43 ∷ []) (lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at04133041 c4) ▸ done


-- F2 K3|CS02: 1 steps
lem-F2-K3∣CS02 : Complete 4 → ⟪ (CK43 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ CK43 ∷ []) ⟫ʷ
lem-F2-K3∣CS02 c4 = run b0
  where
  b0 : Chain (CK43 ∷ Sb1-0-42-3 ∷ []) (Sb1-0-42-3 ∷ CK43 ∷ [])
  b0 = at 0 2 (Sb1-0-42-3 ∷ CK43 ∷ []) (lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at0413213042 c4) ▸ done


-- F2 K3|CS12: 1 steps
lem-F2-K3∣CS12 : Complete 4 → ⟪ (CK43 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CK43 ∷ []) ⟫ʷ
lem-F2-K3∣CS12 c4 = run b0
  where
  b0 : Chain (CK43 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ CK43 ∷ [])
  b0 = at 0 2 (Sb0-1-42-3 ∷ CK43 ∷ []) (lem-auto-CK01-∣-SBOX⟨2·3·04·1⟩-at0413203142 c4) ▸ done


-- auto BOX(0;1234) | CSd31: 5 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd31 : Complete 4 → ⟪ (Bx0-1234 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd31 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (CS13⁻ ∷ []) (lw4 c4 (CS13⁻ ∷ []) (CS13⁻ ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 0 2 (CS13⁻ ∷ Bx0-1324 ∷ []) (sym (lem-CSd12-beta-at2332 c4)) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸
       at 0 1 (CS13⁻ ∷ []) (lw4 c4 (CS13⁻ ∷ []) (CS13⁻ ∷ []) tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CSd31 @0110: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd31-at0110 : Complete 4 → ⟪ (Bx1-0234 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ Bx1-0234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd31-at0110 c4 = run b0
  where
  b0 : Chain (Bx1-0234 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Bx1-0234 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0234⟩ c4) ▸
       at 2 2 (CS13⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS03⁻ ∷ []) (CS13⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS13⁻ ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd31 c4) ▸
       at 0 2 (CS03⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS13⁻ ∷ []) (CS03⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CSd31 @021021: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd31-at021021 : Complete 4 → ⟪ (Bx2-0134 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ Bx2-0134 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd31-at021021 c4 = run b0
  where
  b0 : Chain (Bx2-0134 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Bx2-0134 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0134⟩ c4) ▸
       at 2 2 (CS03⁻ ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS03⁻ ∷ Bx1-0234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd31-at0110 c4) ▸
       at 0 2 (CS03⁻ ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-0134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CSd31 @03102132: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd31-at03102132 : Complete 4 → ⟪ (Bx3-0124 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ Bx3-0124 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd31-at03102132 c4 = run b0
  where
  b0 : Chain (Bx3-0124 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ Bx3-0124 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-0134 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0124⟩ c4) ▸
       at 2 2 (CS03⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd02 c4) ▸
       at 1 2 (CS03⁻ ∷ Bx2-0134 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd31-at021021 c4) ▸
       at 0 2 (CS02⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd03 c4) ▸
       at 1 2 (Bx3-0124 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0134⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CSd31 @0410213243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd31-at0410213243 : Complete 4 → ⟪ (Bx4-0123 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ Bx4-0123 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd31-at0410213243 c4 = run b0
  where
  b0 : Chain (Bx4-0123 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ Bx4-0123 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-0124 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·0123⟩ c4) ▸
       at 2 2 (CS02⁻ ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (Swap))) ▸
       at 1 2 (CS02⁻ ∷ Bx3-0124 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd31-at03102132 c4) ▸
       at 0 2 (CS02⁻ ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (Swap))) ▸
       at 1 2 (Bx4-0123 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·0124⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CSd31 @04103143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd31-at04103143 : Complete 4 → ⟪ (Bx4-0213 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ Bx4-0213 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd31-at04103143 c4 = run b0
  where
  b0 : Chain (Bx4-0213 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ Bx4-0213 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-0123 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0213⟩ c4) ▸
       at 2 2 (CS02⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd01 c4) ▸
       at 1 2 (CS02⁻ ∷ Bx4-0123 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd31-at0410213243 c4) ▸
       at 0 2 (CS01⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd02 c4) ▸
       at 1 2 (Bx4-0213 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0123⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CSd31 @0410233142: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd31-at0410233142 : Complete 4 → ⟪ (Bx4-0312 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ Bx4-0312 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd31-at0410233142 c4 = run b0
  where
  b0 : Chain (Bx4-0312 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ Bx4-0312 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-0213 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0312⟩ c4) ▸
       at 2 2 (CS01⁻ ∷ Sw23 ∷ []) (sym (c₂ (CS • CS • CS) (Swap))) ▸
       at 1 2 (CS01⁻ ∷ Bx4-0213 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd31-at04103143 c4) ▸
       at 0 2 (CS01⁻ ∷ Sw23 ∷ []) (sym (c₂ (CS • CS • CS) (Swap))) ▸
       at 1 2 (Bx4-0312 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0213⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CSd31 @0410233241: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd31-at0410233241 : Complete 4 → ⟪ (Bx4-0321 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ Bx4-0321 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd31-at0410233241 c4 = run b0
  where
  b0 : Chain (Bx4-0321 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ Bx4-0321 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-0312 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0321⟩ c4) ▸
       at 2 2 (CS01⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd02 c4) ▸
       at 1 2 (CS01⁻ ∷ Bx4-0312 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd31-at0410233142 c4) ▸
       at 0 2 (CS02⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd01 c4) ▸
       at 1 2 (Bx4-0321 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0312⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CSd31 @04233240: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd31-at04233240 : Complete 4 → ⟪ (Bx4-1320 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ Bx4-1320 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd31-at04233240 c4 = run b0
  where
  b0 : Chain (Bx4-1320 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ Bx4-1320 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-0321 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·1320⟩ c4) ▸
       at 2 2 (CS02⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS12⁻ ∷ []) (CS02⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS02⁻ ∷ Bx4-0321 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd31-at0410233241 c4) ▸
       at 0 2 (CS12⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS02⁻ ∷ []) (CS12⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-1320 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·0321⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CS01 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS01-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS01-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CS01 ∷ []) (CS01 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (CS01 ∷ Sw23 ∷ []) (sym (c₂ (CS) (Swap))) ▸
       at 1 2 (CS01 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS01 c4) ▸
       at 0 2 (CS01 ∷ Sw23 ∷ []) (sym (c₂ (CS) (Swap))) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CCZ102: 38 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ102 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ102 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (run b4))))
  where
  b0 : Chain (Sb0-1-23-4 ∷ CCZ012 ∷ []) (CS12 ∷ Bx4-1320 ∷ Toff023 ∷ Sb4-1-0-2 ∷ Toff023 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ Sb⁻4-1-0-2 ∷ CS01 ∷ [])
  b0 = at 1 1 (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS12 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS31-at2332 c4) ▸
       at 1 1 (Sb4-1-32-0 ∷ []) (lem-F0-at0112203443 c4) ▸
       at 1 1 (Bx4-1320 ∷ Toff023 ∷ Sb4-1-0-2 ∷ Toff023 ∷ Sb⁻4-1-0-2 ∷ []) (refl) ▸
       at 5 1 (CS01⁻ ∷ []) (refl) ▸
       at 5 4 (CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01⁻ ∷ []) (lw4 c4 (CS01⁻ ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ []) (CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01⁻ ∷ []) tt tt Eq.refl) ▸
       at 8 1 (Sb⁻4-1-0-2 ∷ []) (refl) ▸ done

  b1 : Chain (CS12 ∷ Bx4-1320 ∷ Toff023 ∷ Sb4-1-0-2 ∷ Toff023 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ Sb⁻4-1-0-2 ∷ CS01 ∷ []) (CS12 ∷ CX02 ∷ Bx4-1023 ∷ CCZ013 ∷ CS12⁻ ∷ CX02 ∷ Toff023 ∷ Sb4-1-0-2 ∷ Toff023 ∷ Sb⁻4-1-0-2 ∷ CS01 ∷ [])
  b1 = at 3 1 (CS01 ∷ []) (refl) ▸
       at 2 6 (CX02 ∷ CS12⁻ ∷ CX02 ∷ Toff023 ∷ CS01 ∷ Toff023 ∷ []) (lw4 c4 (Toff023 ∷ CS01 ∷ Toff023 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ []) (CX02 ∷ CS12⁻ ∷ CX02 ∷ Toff023 ∷ CS01 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sb4-1-0-2 ∷ []) (refl) ▸
       at 1 0 (CX02 ∷ CX02 ∷ []) (lw4 c4 [] (CX02 ∷ CX02 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Bx4-1230 ∷ []) (lem-sym23-at04233240 c4) ▸
       at 3 1 (Bx4-1203 ∷ []) (lem-sym34-at0440 c4) ▸
       at 3 1 (Bx4-1023 ∷ []) (lem-sym23-at043043 c4) ▸
       at 2 3 (Bx4-1023 ∷ CCZ013 ∷ []) (lem-CX23-beta-at04203243 c4) ▸ done

  b2 : Chain (CS12 ∷ CX02 ∷ Bx4-1023 ∷ CCZ013 ∷ CS12⁻ ∷ CX02 ∷ Toff023 ∷ Sb4-1-0-2 ∷ Toff023 ∷ Sb⁻4-1-0-2 ∷ CS01 ∷ []) (CS12 ∷ CX02 ∷ CCZ013 ∷ CS12⁻ ∷ CX02 ∷ CX02 ∷ Bx4-1203 ∷ CX02 ∷ Toff023 ∷ Sb4-1-0-2 ∷ Toff023 ∷ Sb⁻4-1-0-2 ∷ CS01 ∷ [])
  b2 = at 2 1 (Bx4-1203 ∷ []) (lem-sym23-at04203243 c4) ▸
       at 2 1 (Bx4-1230 ∷ []) (lem-sym34-at043043 c4) ▸
       at 2 1 (Bx4-1320 ∷ []) (lem-sym23-at0440 c4) ▸
       at 2 2 (CCZ013 ∷ Bx4-1320 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ142-at04233240 c4) ▸
       at 3 2 (CS12⁻ ∷ Bx4-1320 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd31-at04233240 c4) ▸
       at 4 0 (CX02 ∷ CX02 ∷ []) (lw4 c4 [] (CX02 ∷ CX02 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Bx4-1230 ∷ []) (lem-sym23-at04233240 c4) ▸
       at 6 1 (Bx4-1203 ∷ []) (lem-sym34-at0440 c4) ▸ done

  b3 : Chain (CS12 ∷ CX02 ∷ CCZ013 ∷ CS12⁻ ∷ CX02 ∷ CX02 ∷ Bx4-1203 ∷ CX02 ∷ Toff023 ∷ Sb4-1-0-2 ∷ Toff023 ∷ Sb⁻4-1-0-2 ∷ CS01 ∷ []) (CS12 ∷ CCZ013 ∷ CCZ013 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ Bx4-1320 ∷ Toff023 ∷ Sb4-1-0-2 ∷ Toff023 ∷ Sb⁻4-1-0-2 ∷ CS01 ∷ [])
  b3 = at 6 1 (Bx4-1023 ∷ []) (lem-sym23-at043043 c4) ▸
       at 5 3 (Bx4-1023 ∷ CCZ013 ∷ []) (lem-CX23-beta-at04203243 c4) ▸
       at 5 1 (Bx4-1203 ∷ []) (lem-sym23-at04203243 c4) ▸
       at 5 1 (Bx4-1230 ∷ []) (lem-sym34-at043043 c4) ▸
       at 5 1 (Bx4-1320 ∷ []) (lem-sym23-at0440 c4) ▸
       at 5 2 (CCZ013 ∷ Bx4-1320 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ142-at04233240 c4) ▸
       at 1 2 (CCZ013 ∷ CX02 ∷ []) (lw4 c4 (CX02 ∷ CCZ013 ∷ []) (CCZ013 ∷ CX02 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (CCZ013 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ []) (lw4 c4 (CX02 ∷ CS12⁻ ∷ CX02 ∷ CCZ013 ∷ []) (CCZ013 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ []) tt tt Eq.refl) ▸ done

  b4 : Chain (CS12 ∷ CCZ013 ∷ CCZ013 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ Bx4-1320 ∷ Toff023 ∷ Sb4-1-0-2 ∷ Toff023 ∷ Sb⁻4-1-0-2 ∷ CS01 ∷ []) (CCZ012 ∷ Sb0-1-23-4 ∷ [])
  b4 = at 1 2 [] (lw4 c4 (CCZ013 ∷ CCZ013 ∷ []) [] tt tt Eq.refl) ▸
       at 4 5 (Sb4-1-32-0 ∷ []) (refl) ▸
       at 4 1 (Sb0-1-32-4 ∷ []) (sym (lem-F0-at0112203443 c4)) ▸
       at 4 2 (CS01 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS01-at2332 c4) ▸
       at 5 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 5 (CCZ012 ∷ []) (lw4 c4 (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ143: 5 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ143 : Complete 4 → ⟪ (Bx0-1234 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ143 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CCZ134 ∷ []) (CCZ134 ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ []) (lw0 c4 (CCZ134 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 0 2 (CCZ134 ∷ Bx0-1324 ∷ []) (sym (lem-c124-beta-at2332 c4)) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸
       at 0 1 (CCZ134 ∷ []) (lw0 c4 (CCZ134 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CSd21: 3 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd21 : Complete 4 → ⟪ (Bx0-1234 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd21 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (CS12⁻ ∷ []) (lw4 c4 (CS12⁻ ∷ []) (CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 0 2 (CS12⁻ ∷ Bx0-1234 ∷ []) (sym (lem-CSd12-beta c4)) ▸
       at 0 1 (CS12⁻ ∷ []) (lw4 c4 (CS12⁻ ∷ []) (CS12⁻ ∷ []) tt tt Eq.refl) ▸ done


-- sym34 @0410233142: 5 steps
lem-sym34-at0410233142 : Complete 4 → ⟪ (Bx4-0312 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0321 ∷ []) ⟫ʷ
lem-sym34-at0410233142 c4 = run b0
  where
  b0 : Chain (Bx4-0312 ∷ []) (Bx4-0321 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-0213 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0312⟩ c4) ▸
       at 1 1 (Bx4-0231 ∷ []) (lem-sym34-at04103143 c4) ▸
       at 0 2 (Bx4-0321 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0231⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym34 @0410233241: 5 steps
lem-sym34-at0410233241 : Complete 4 → ⟪ (Bx4-0321 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0312 ∷ []) ⟫ʷ
lem-sym34-at0410233241 c4 = run b0
  where
  b0 : Chain (Bx4-0321 ∷ []) (Bx4-0312 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-0312 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0321⟩ c4) ▸
       at 1 1 (Bx4-0321 ∷ []) (lem-sym34-at0410233142 c4) ▸
       at 0 2 (Bx4-0312 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0321⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym34 @04233240: 5 steps
lem-sym34-at04233240 : Complete 4 → ⟪ (Bx4-1320 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1302 ∷ []) ⟫ʷ
lem-sym34-at04233240 c4 = run b0
  where
  b0 : Chain (Bx4-1320 ∷ []) (Bx4-1302 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-0321 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·1320⟩ c4) ▸
       at 1 1 (Bx4-0312 ∷ []) (lem-sym34-at0410233241 c4) ▸
       at 0 2 (Bx4-1302 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·0312⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @04233042: 5 steps
lem-sym23-at04233042 : Complete 4 → ⟪ (Bx4-1302 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1032 ∷ []) ⟫ʷ
lem-sym23-at04233042 c4 = run b0
  where
  b0 : Chain (Bx4-1302 ∷ []) (Bx4-1032 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-0312 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·1302⟩ c4) ▸
       at 1 1 (Bx4-0132 ∷ []) (lem-sym23-at0410233142 c4) ▸
       at 0 2 (Bx4-1032 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·0132⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- CX23-beta @04102142: 8 steps
lem-CX23-beta-at04102142 : Complete 4 → ⟪ (CX13 ∷ Bx4-0132 ∷ CX13 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0132 ∷ CCZ012 ∷ []) ⟫ʷ
lem-CX23-beta-at04102142 c4 = run b0
  where
  b0 : Chain (CX13 ∷ Bx4-0132 ∷ CX13 ∷ []) (Bx4-0132 ∷ CCZ012 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CX12 ∷ Sw23 ∷ []) (lem-nat-2-CX13 c4) ▸
       at 2 2 (Bx4-0123 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0132⟩ c4) ▸
       at 3 2 (CX12 ∷ Sw23 ∷ []) (lem-nat-2-CX13 c4) ▸
       at 1 3 (Bx4-0123 ∷ CCZ013 ∷ []) (lem-CX23-beta-at0410213243 c4) ▸
       at 0 2 (Bx4-0132 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0123⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- CX23-beta @042042: 8 steps
lem-CX23-beta-at042042 : Complete 4 → ⟪ (CX03 ∷ Bx4-1032 ∷ CX03 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1032 ∷ CCZ012 ∷ []) ⟫ʷ
lem-CX23-beta-at042042 c4 = run b0
  where
  b0 : Chain (CX03 ∷ Bx4-1032 ∷ CX03 ∷ []) (Bx4-1032 ∷ CCZ012 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CX13 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CX03 ∷ []) (CX13 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx4-0132 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·1032⟩ c4) ▸
       at 3 2 (CX13 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CX03 ∷ []) (CX13 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Bx4-0132 ∷ CCZ012 ∷ []) (lem-CX23-beta-at04102142 c4) ▸
       at 0 2 (Bx4-1032 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·0132⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @042042: 5 steps
lem-sym23-at042042 : Complete 4 → ⟪ (Bx4-1032 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1302 ∷ []) ⟫ʷ
lem-sym23-at042042 c4 = run b0
  where
  b0 : Chain (Bx4-1032 ∷ []) (Bx4-1302 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-0132 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·1032⟩ c4) ▸
       at 1 1 (Bx4-0312 ∷ []) (lem-sym23-at04102142 c4) ▸
       at 0 2 (Bx4-1302 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·0312⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym34 @04233042: 5 steps
lem-sym34-at04233042 : Complete 4 → ⟪ (Bx4-1302 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1320 ∷ []) ⟫ʷ
lem-sym34-at04233042 c4 = run b0
  where
  b0 : Chain (Bx4-1302 ∷ []) (Bx4-1320 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-0312 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·1302⟩ c4) ▸
       at 1 1 (Bx4-0321 ∷ []) (lem-sym34-at0410233142 c4) ▸
       at 0 2 (Bx4-1320 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·0321⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ143 @0110: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ143-at0110 : Complete 4 → ⟪ (Bx1-0234 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Bx1-0234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ143-at0110 c4 = run b0
  where
  b0 : Chain (Bx1-0234 ∷ CCZ034 ∷ []) (CCZ034 ∷ Bx1-0234 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0234⟩ c4) ▸
       at 2 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 1 2 (CCZ134 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ143 c4) ▸
       at 0 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 1 2 (Bx1-0234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ143 @021021: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ143-at021021 : Complete 4 → ⟪ (Bx2-0134 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Bx2-0134 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ143-at021021 c4 = run b0
  where
  b0 : Chain (Bx2-0134 ∷ CCZ034 ∷ []) (CCZ034 ∷ Bx2-0134 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0134⟩ c4) ▸
       at 2 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 1 2 (CCZ034 ∷ Bx1-0234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ143-at0110 c4) ▸
       at 0 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 1 2 (Bx2-0134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ143 @03102132: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ143-at03102132 : Complete 4 → ⟪ (Bx3-0124 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Bx3-0124 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ143-at03102132 c4 = run b0
  where
  b0 : Chain (Bx3-0124 ∷ CCZ024 ∷ []) (CCZ024 ∷ Bx3-0124 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-0134 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0124⟩ c4) ▸
       at 2 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 1 2 (CCZ034 ∷ Bx2-0134 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ143-at021021 c4) ▸
       at 0 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 1 2 (Bx3-0124 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0134⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ143 @0410213243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ143-at0410213243 : Complete 4 → ⟪ (Bx4-0123 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Bx4-0123 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ143-at0410213243 c4 = run b0
  where
  b0 : Chain (Bx4-0123 ∷ CCZ023 ∷ []) (CCZ023 ∷ Bx4-0123 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-0124 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·0123⟩ c4) ▸
       at 2 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4) ▸
       at 1 2 (CCZ024 ∷ Bx3-0124 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ143-at03102132 c4) ▸
       at 0 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 1 2 (Bx4-0123 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·0124⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ143 @04103143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ143-at04103143 : Complete 4 → ⟪ (Bx4-0213 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Bx4-0213 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ143-at04103143 c4 = run b0
  where
  b0 : Chain (Bx4-0213 ∷ CCZ013 ∷ []) (CCZ013 ∷ Bx4-0213 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-0123 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0213⟩ c4) ▸
       at 2 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 1 2 (CCZ023 ∷ Bx4-0123 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ143-at0410213243 c4) ▸
       at 0 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 1 2 (Bx4-0213 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0123⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ143 @0410233142: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ143-at0410233142 : Complete 4 → ⟪ (Bx4-0312 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Bx4-0312 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ143-at0410233142 c4 = run b0
  where
  b0 : Chain (Bx4-0312 ∷ CCZ012 ∷ []) (CCZ012 ∷ Bx4-0312 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-0213 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0312⟩ c4) ▸
       at 2 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 1 2 (CCZ013 ∷ Bx4-0213 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ143-at04103143 c4) ▸
       at 0 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 1 2 (Bx4-0312 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0213⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ143 @0410233241: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ143-at0410233241 : Complete 4 → ⟪ (Bx4-0321 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Bx4-0321 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ143-at0410233241 c4 = run b0
  where
  b0 : Chain (Bx4-0321 ∷ CCZ012 ∷ []) (CCZ012 ∷ Bx4-0321 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-0312 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0321⟩ c4) ▸
       at 2 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Bx4-0312 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ143-at0410233142 c4) ▸
       at 0 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-0321 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0312⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ143 @04233240: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ143-at04233240 : Complete 4 → ⟪ (Bx4-1320 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Bx4-1320 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ143-at04233240 c4 = run b0
  where
  b0 : Chain (Bx4-1320 ∷ CCZ012 ∷ []) (CCZ012 ∷ Bx4-1320 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-0321 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·1320⟩ c4) ▸
       at 2 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Bx4-0321 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ143-at0410233241 c4) ▸
       at 0 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-1320 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·0321⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CSd21 @0110: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd21-at0110 : Complete 4 → ⟪ (Bx1-0234 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ Bx1-0234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd21-at0110 c4 = run b0
  where
  b0 : Chain (Bx1-0234 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ Bx1-0234 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0234⟩ c4) ▸
       at 2 2 (CS12⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS02⁻ ∷ []) (CS12⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS12⁻ ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd21 c4) ▸
       at 0 2 (CS02⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS12⁻ ∷ []) (CS02⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CSd21 @021021: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd21-at021021 : Complete 4 → ⟪ (Bx2-0134 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ Bx2-0134 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd21-at021021 c4 = run b0
  where
  b0 : Chain (Bx2-0134 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ Bx2-0134 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0134⟩ c4) ▸
       at 2 2 (CS02⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd01 c4) ▸
       at 1 2 (CS02⁻ ∷ Bx1-0234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd21-at0110 c4) ▸
       at 0 2 (CS01⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd02 c4) ▸
       at 1 2 (Bx2-0134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CSd21 @03102132: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd21-at03102132 : Complete 4 → ⟪ (Bx3-0124 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ Bx3-0124 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd21-at03102132 c4 = run b0
  where
  b0 : Chain (Bx3-0124 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ Bx3-0124 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-0134 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0124⟩ c4) ▸
       at 2 2 (CS01⁻ ∷ Sw23 ∷ []) (sym (c₂ (CS • CS • CS) (Swap))) ▸
       at 1 2 (CS01⁻ ∷ Bx2-0134 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd21-at021021 c4) ▸
       at 0 2 (CS01⁻ ∷ Sw23 ∷ []) (sym (c₂ (CS • CS • CS) (Swap))) ▸
       at 1 2 (Bx3-0124 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0134⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CSd21 @0410213243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd21-at0410213243 : Complete 4 → ⟪ (Bx4-0123 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ Bx4-0123 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd21-at0410213243 c4 = run b0
  where
  b0 : Chain (Bx4-0123 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ Bx4-0123 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-0124 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·0123⟩ c4) ▸
       at 2 2 (CS01⁻ ∷ Sw34 ∷ []) (sym (c₂ (CS • CS • CS) (Swap ↑))) ▸
       at 1 2 (CS01⁻ ∷ Bx3-0124 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd21-at03102132 c4) ▸
       at 0 2 (CS01⁻ ∷ Sw34 ∷ []) (sym (c₂ (CS • CS • CS) (Swap ↑))) ▸
       at 1 2 (Bx4-0123 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·0124⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CSd21 @04103143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd21-at04103143 : Complete 4 → ⟪ (Bx4-0213 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ Bx4-0213 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd21-at04103143 c4 = run b0
  where
  b0 : Chain (Bx4-0213 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ Bx4-0213 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-0123 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0213⟩ c4) ▸
       at 2 2 (CS01⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd02 c4) ▸
       at 1 2 (CS01⁻ ∷ Bx4-0123 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd21-at0410213243 c4) ▸
       at 0 2 (CS02⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd01 c4) ▸
       at 1 2 (Bx4-0213 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0123⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CSd21 @0410233142: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd21-at0410233142 : Complete 4 → ⟪ (Bx4-0312 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ Bx4-0312 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd21-at0410233142 c4 = run b0
  where
  b0 : Chain (Bx4-0312 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Bx4-0312 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-0213 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0312⟩ c4) ▸
       at 2 2 (CS02⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd03 c4) ▸
       at 1 2 (CS02⁻ ∷ Bx4-0213 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd21-at04103143 c4) ▸
       at 0 2 (CS03⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd02 c4) ▸
       at 1 2 (Bx4-0312 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0213⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CSd21 @0410233241: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd21-at0410233241 : Complete 4 → ⟪ (Bx4-0321 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ Bx4-0321 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd21-at0410233241 c4 = run b0
  where
  b0 : Chain (Bx4-0321 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Bx4-0321 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-0312 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0321⟩ c4) ▸
       at 2 2 (CS03⁻ ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS03⁻ ∷ Bx4-0312 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd21-at0410233142 c4) ▸
       at 0 2 (CS03⁻ ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-0321 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0312⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CSd21 @04233240: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd21-at04233240 : Complete 4 → ⟪ (Bx4-1320 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ Bx4-1320 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd21-at04233240 c4 = run b0
  where
  b0 : Chain (Bx4-1320 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ Bx4-1320 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-0321 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·1320⟩ c4) ▸
       at 2 2 (CS03⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS13⁻ ∷ []) (CS03⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS03⁻ ∷ Bx4-0321 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd21-at0410233241 c4) ▸
       at 0 2 (CS13⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS03⁻ ∷ []) (CS13⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-1320 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·0321⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CCZ103: 34 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ103 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ103 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (run b4))))
  where
  b0 : Chain (Sb0-1-23-4 ∷ CCZ013 ∷ []) (CS13 ∷ Bx4-1320 ∷ Toff023 ∷ Sb4-1-0-2 ∷ Toff023 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ Sb⁻4-1-0-2 ∷ CS01 ∷ [])
  b0 = at 1 1 (CS13 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ []) (lw4 c4 (CCZ013 ∷ []) (CS13 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS13 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS21-at2332 c4) ▸
       at 1 1 (Sb4-1-32-0 ∷ []) (lem-F0-at0112203443 c4) ▸
       at 1 1 (Bx4-1320 ∷ Toff023 ∷ Sb4-1-0-2 ∷ Toff023 ∷ Sb⁻4-1-0-2 ∷ []) (refl) ▸
       at 5 1 (CS01⁻ ∷ []) (refl) ▸
       at 5 4 (CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01⁻ ∷ []) (lw4 c4 (CS01⁻ ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ []) (CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01⁻ ∷ []) tt tt Eq.refl) ▸
       at 8 1 (Sb⁻4-1-0-2 ∷ []) (refl) ▸ done

  b1 : Chain (CS13 ∷ Bx4-1320 ∷ Toff023 ∷ Sb4-1-0-2 ∷ Toff023 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ Sb⁻4-1-0-2 ∷ CS01 ∷ []) (CS13 ∷ CX03 ∷ Bx4-1302 ∷ CCZ012 ∷ CS13⁻ ∷ CX03 ∷ Toff023 ∷ Sb4-1-0-2 ∷ Toff023 ∷ Sb⁻4-1-0-2 ∷ CS01 ∷ [])
  b1 = at 3 1 (CS01 ∷ []) (refl) ▸
       at 2 6 (CX03 ∷ CS13⁻ ∷ CX03 ∷ Toff023 ∷ CS01 ∷ Toff023 ∷ []) (lw4 c4 (Toff023 ∷ CS01 ∷ Toff023 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ []) (CX03 ∷ CS13⁻ ∷ CX03 ∷ Toff023 ∷ CS01 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sb4-1-0-2 ∷ []) (refl) ▸
       at 1 0 (CX03 ∷ CX03 ∷ []) (lw4 c4 [] (CX03 ∷ CX03 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Bx4-1302 ∷ []) (lem-sym34-at04233240 c4) ▸
       at 3 1 (Bx4-1032 ∷ []) (lem-sym23-at04233042 c4) ▸
       at 2 3 (Bx4-1032 ∷ CCZ012 ∷ []) (lem-CX23-beta-at042042 c4) ▸
       at 2 1 (Bx4-1302 ∷ []) (lem-sym23-at042042 c4) ▸ done

  b2 : Chain (CS13 ∷ CX03 ∷ Bx4-1302 ∷ CCZ012 ∷ CS13⁻ ∷ CX03 ∷ Toff023 ∷ Sb4-1-0-2 ∷ Toff023 ∷ Sb⁻4-1-0-2 ∷ CS01 ∷ []) (CS13 ∷ CX03 ∷ CCZ012 ∷ CS13⁻ ∷ CX03 ∷ Bx4-1302 ∷ CCZ012 ∷ Toff023 ∷ Sb4-1-0-2 ∷ Toff023 ∷ Sb⁻4-1-0-2 ∷ CS01 ∷ [])
  b2 = at 2 1 (Bx4-1320 ∷ []) (lem-sym34-at04233042 c4) ▸
       at 2 2 (CCZ012 ∷ Bx4-1320 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ143-at04233240 c4) ▸
       at 3 2 (CS13⁻ ∷ Bx4-1320 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd21-at04233240 c4) ▸
       at 4 0 (CX03 ∷ CX03 ∷ []) (lw4 c4 [] (CX03 ∷ CX03 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Bx4-1302 ∷ []) (lem-sym34-at04233240 c4) ▸
       at 6 1 (Bx4-1032 ∷ []) (lem-sym23-at04233042 c4) ▸
       at 5 3 (Bx4-1032 ∷ CCZ012 ∷ []) (lem-CX23-beta-at042042 c4) ▸
       at 5 1 (Bx4-1302 ∷ []) (lem-sym23-at042042 c4) ▸ done

  b3 : Chain (CS13 ∷ CX03 ∷ CCZ012 ∷ CS13⁻ ∷ CX03 ∷ Bx4-1302 ∷ CCZ012 ∷ Toff023 ∷ Sb4-1-0-2 ∷ Toff023 ∷ Sb⁻4-1-0-2 ∷ CS01 ∷ []) (CS13 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ Sb0-1-32-4 ∷ [])
  b3 = at 5 1 (Bx4-1320 ∷ []) (lem-sym34-at04233042 c4) ▸
       at 5 2 (CCZ012 ∷ Bx4-1320 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ143-at04233240 c4) ▸
       at 1 2 (CCZ012 ∷ CX03 ∷ []) (lw4 c4 (CX03 ∷ CCZ012 ∷ []) (CCZ012 ∷ CX03 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (CCZ012 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ []) (lw4 c4 (CX03 ∷ CS13⁻ ∷ CX03 ∷ CCZ012 ∷ []) (CCZ012 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ []) tt tt Eq.refl) ▸
       at 1 2 [] (lw4 c4 (CCZ012 ∷ CCZ012 ∷ []) [] tt tt Eq.refl) ▸
       at 4 5 (Sb4-1-32-0 ∷ []) (refl) ▸
       at 4 1 (Sb0-1-32-4 ∷ []) (sym (lem-F0-at0112203443 c4)) ▸
       at 4 2 (CS01 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS01-at2332 c4) ▸ done

  b4 : Chain (CS13 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ Sb0-1-32-4 ∷ []) (CCZ013 ∷ Sb0-1-23-4 ∷ [])
  b4 = at 5 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 5 (CCZ013 ∷ []) (lw4 c4 (CS13 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CSd21 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd21-at2332 : Complete 4 → ⟪ (Bx0-1324 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd21-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ c4) ▸
       at 2 2 (CS12⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd13 c4) ▸
       at 1 2 (CS12⁻ ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd21 c4) ▸
       at 0 2 (CS13⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd12 c4) ▸
       at 1 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CCZ123: 30 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ123 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ123 c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Sb0-1-23-4 ∷ CCZ123 ∷ []) (CS13 ∷ Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS12 ∷ [])
  b0 = at 1 1 (CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ CS12 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS13 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS21-at2332 c4) ▸
       at 1 1 (Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ []) (refl) ▸
       at 5 1 (CS14⁻ ∷ []) (refl) ▸
       at 5 4 (CX23 ∷ CS13⁻ ∷ CX23 ∷ CS14⁻ ∷ []) (lw0 c4 (CS14⁻ ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ []) (CX23 ∷ CS13⁻ ∷ CX23 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 8 1 (Sb⁻0-1-4-2 ∷ []) (refl) ▸
       at 4 4 (CX23 ∷ CS13⁻ ∷ CX23 ∷ Toff423 ∷ []) (lw0 c4 (Toff423 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ []) (CX23 ∷ CS13⁻ ∷ CX23 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CS13 ∷ Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS12 ∷ []) (CS13 ∷ CX23 ∷ Bx0-1324 ∷ CCZ124 ∷ CS13⁻ ∷ CX23 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS12 ∷ [])
  b1 = at 3 1 (CS14 ∷ []) (refl) ▸
       at 3 4 (CX23 ∷ CS13⁻ ∷ CX23 ∷ CS14 ∷ []) (lw0 c4 (CS14 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ []) (CX23 ∷ CS13⁻ ∷ CX23 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sb0-1-4-2 ∷ []) (refl) ▸
       at 2 4 (CX23 ∷ CS13⁻ ∷ CX23 ∷ Toff423 ∷ []) (lw0 c4 (Toff423 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ []) (CX23 ∷ CS13⁻ ∷ CX23 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 1 0 (CX23 ∷ CX23 ∷ []) (lw4 c4 [] (CX23 ∷ CX23 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸
       at 2 3 (Bx0-1234 ∷ CCZ124 ∷ []) (lem-CX23-beta c4) ▸
       at 2 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸ done

  b2 : Chain (CS13 ∷ CX23 ∷ Bx0-1324 ∷ CCZ124 ∷ CS13⁻ ∷ CX23 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS12 ∷ []) (CS13 ∷ CCZ124 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ CCZ124 ∷ Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS12 ∷ [])
  b2 = at 2 2 (CCZ124 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at2332 c4) ▸
       at 3 2 (CS13⁻ ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd21-at2332 c4) ▸
       at 4 0 (CX23 ∷ CX23 ∷ []) (lw4 c4 [] (CX23 ∷ CX23 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸
       at 5 3 (Bx0-1234 ∷ CCZ124 ∷ []) (lem-CX23-beta c4) ▸
       at 5 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 5 2 (CCZ124 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at2332 c4) ▸
       at 1 2 (CCZ124 ∷ CX23 ∷ []) (lw0 c4 (CX23 ∷ CCZ124 ∷ []) (CCZ124 ∷ CX23 ∷ []) tt tt Eq.refl) ▸ done

  b3 : Chain (CS13 ∷ CCZ124 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ CCZ124 ∷ Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS12 ∷ []) (CCZ123 ∷ Sb0-1-23-4 ∷ [])
  b3 = at 2 4 (CCZ124 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ []) (lw0 c4 (CX23 ∷ CS13⁻ ∷ CX23 ∷ CCZ124 ∷ []) (CCZ124 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 [] (lw0 c4 (CCZ124 ∷ CCZ124 ∷ []) [] tt tt Eq.refl) ▸
       at 4 5 (Sb0-1-32-4 ∷ []) (refl) ▸
       at 4 2 (CS12 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS31-at2332 c4) ▸
       at 5 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 5 (CCZ123 ∷ []) (lw4 c4 (CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ CS12 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸ done


-- CX23-beta @2442: 8 steps
lem-CX23-beta-at2442 : Complete 4 → ⟪ (CX43 ∷ Bx0-1432 ∷ CX43 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CX23-beta-at2442 c4 = run b0
  where
  b0 : Chain (CX43 ∷ Bx0-1432 ∷ CX43 ∷ []) (Bx0-1432 ∷ CCZ124 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CX42 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CX43 ∷ []) (CX42 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-1423 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1432⟩ c4) ▸
       at 3 2 (CX42 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CX43 ∷ []) (CX42 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Bx0-1423 ∷ CCZ134 ∷ []) (lem-CX23-beta-at243243 c4) ▸
       at 0 2 (Bx0-1432 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1423⟩ c4) ▸
       at 1 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


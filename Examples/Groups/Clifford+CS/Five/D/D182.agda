{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D182 where

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
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-sym12-at0110 ; lem-sym12-at011220 ; lem-sym23-at0110243243 ; lem-sym23-at01103443)
open import Examples.Groups.Clifford+CS.Five.D.D007 using (lem-SBsym-at0113203442 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at2332 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd4-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D010 using (lem-CS20-beta-ci-at011220)
open import Examples.Groups.Clifford+CS.Five.D.D011 using (lem-beta-T-at01103443 ; lem-sym34-at0110243243 ; lem-sym34-at01102442)
open import Examples.Groups.Clifford+CS.Five.D.D013 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D137 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ413)
open import Examples.Groups.Clifford+CS.Five.D.D156 using (lem-beta-T-at01102442)
open import Examples.Groups.Clifford+CS.Five.D.D181 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at01102442)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-2-CCZ124 ; lem-nat-2-CCZ134)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-2-SBOX⟨0·1·23·4⟩ ; lem-nat-2-SBOX⟨0·1·32·4⟩)
open import Examples.Groups.Clifford+CS.Five.D.R017 using (lem-nat-2-BOX⟨1·0234⟩)
open import Examples.Groups.Clifford+CS.Five.D.R020 using (lem-nat-2-SBOX⟨0·1·42·3⟩ ; lem-nat-2-SBOX⟨0·1·43·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R028 using (lem-nat-2-BOX⟨1·0324⟩ ; lem-nat-3-BOX⟨1·0423⟩)
open import Examples.Groups.Clifford+CS.Five.D.R029 using (lem-nat-3-BOX⟨1·0324⟩)
open import Examples.Groups.Clifford+CS.Five.D.R033 using (lem-nat-0-SBOX⟨0·1·43·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R034 using (lem-nat-0-SBOX⟨1·0·43·2⟩)
-- F4 CS03^0|K1^1: 133 steps
lem-F4-CS03ᵖ0∣K1ᵖ1 : Complete 4 → ⟪ (X4 ∷ Sb1-0-43-2 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ Sb1-0-43-2 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS03ᵖ0∣K1ᵖ1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (run b16))))))))))))))))
  where
  b0 : Chain (X4 ∷ Sb1-0-43-2 ∷ X4 ∷ CK41 ∷ []) (ι ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ [])
  b0 = at 3 1 (ι1 ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ []) (pw0 c4 (CK41 ∷ []) (ι1 ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (ι ∷ []) (uₛ (iI ↑) (iI) Eq.refl) ▸
       at 2 2 (ι ∷ X4 ∷ []) (zc) ▸
       at 1 2 (ι ∷ Sb1-0-43-2 ∷ []) (zc) ▸
       at 0 2 (ι ∷ X4 ∷ []) (zc) ▸
       at 2 1 (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 3 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (ι ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ []) (ι ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ S4⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ [])
  b1 = at 9 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 1 (CS02⁻ ∷ []) (refl) ▸
       at 13 4 (S4⁻ ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) (lw3 c4 (X4 ∷ CS02⁻ ∷ X4 ∷ S4⁻ ∷ []) (S4⁻ ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 1 (Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 10 4 (S4⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff234 ∷ X4 ∷ S4⁻ ∷ []) (S4⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 1 (CS02 ∷ []) (refl) ▸
       at 7 4 (S4⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) (lw3 c4 (X4 ∷ CS02 ∷ X4 ∷ S4⁻ ∷ []) (S4⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (ι ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ S4⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ []) (ι ∷ X4 ∷ Toff104 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ S4⁻ ∷ X4 ∷ Toff104 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ [])
  b2 = at 9 1 (Sb1-0-2-3 ∷ []) (refl) ▸
       at 4 4 (S4⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff234 ∷ X4 ∷ S4⁻ ∷ []) (S4⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Toff104 ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ []) (lem-beta-T-at01102442 c4) ▸
       at 3 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 4 (S4⁻ ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CCZ123 ∷ X4 ∷ S4⁻ ∷ []) (S4⁻ ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 4 (S4⁻ ∷ X4 ∷ Toff104 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff104 ∷ X4 ∷ S4⁻ ∷ []) (S4⁻ ∷ X4 ∷ Toff104 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b3 : Chain (ι ∷ X4 ∷ Toff104 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ S4⁻ ∷ X4 ∷ Toff104 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ [])
  b3 = at 4 4 (S4⁻ ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CCZ123 ∷ X4 ∷ S4⁻ ∷ []) (S4⁻ ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (S4⁻ ∷ X4 ∷ Toff104 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff104 ∷ X4 ∷ S4⁻ ∷ []) (S4⁻ ∷ X4 ∷ Toff104 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 3 4 (Bx1-0432 ∷ []) (sym (lem-beta-T-at01102442 c4)) ▸
       at 4 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b4 : Chain (ι ∷ S4⁻ ∷ X4 ∷ Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ [])
  b4 = at 6 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 3 5 (Sb1-0-43-2 ∷ []) (refl) ▸
       at 3 1 (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b5 : Chain (ι ∷ S4⁻ ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ CS14 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ [])
  b5 = at 15 1 (CS02⁻ ∷ []) (refl) ▸
       at 14 4 (CS14 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS02⁻ ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 1 (Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 11 4 (CS14 ∷ X4 ∷ Toff234 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff234 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ Toff234 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 1 (CS02 ∷ []) (refl) ▸
       at 8 4 (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS02 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 1 (Sb1-0-2-3 ∷ []) (refl) ▸
       at 5 4 (CS14 ∷ X4 ∷ Toff234 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff234 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ Toff234 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b6 : Chain (ι ∷ S4⁻ ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ CS14 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ CS14 ∷ X4 ∷ Toff104 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff104 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ [])
  b6 = at 3 1 (Toff104 ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ []) (lem-beta-T-at01102442 c4) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 4 (CS14 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CCZ123 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 4 (CS14 ∷ X4 ∷ Toff104 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff104 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ Toff104 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 4 (CS14 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CCZ123 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (CS14 ∷ X4 ∷ Toff104 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff104 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ Toff104 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b7 : Chain (ι ∷ S4⁻ ∷ CS14 ∷ X4 ∷ Toff104 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff104 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ CS14 ∷ X4 ∷ Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ [])
  b7 = at 5 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 4 4 (Bx1-0432 ∷ []) (sym (lem-beta-T-at01102442 c4)) ▸
       at 5 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b8 : Chain (ι ∷ S4⁻ ∷ CS14 ∷ X4 ∷ Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ CS14 ∷ K1 ∷ CS14 ∷ [])
  b8 = at 4 5 (Sb1-0-43-2 ∷ []) (refl) ▸
       at 5 2 (K1 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ K1 ∷ []) (K1 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (K1 ∷ Sb1-0-43-2 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at01102442 c4) ▸
       at 3 2 (K1 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ K1 ∷ []) (K1 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b9 : Chain (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ CS14 ∷ K1 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K1 ∷ CS14 ∷ [])
  b9 = at 15 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 1 (CS02⁻ ∷ []) (refl) ▸
       at 16 4 (CS14 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS02⁻ ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 18 1 (Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 13 4 (CS14 ∷ X4 ∷ Toff234 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff234 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ Toff234 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 1 (CS02 ∷ []) (refl) ▸
       at 10 4 (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS02 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 1 (Sb1-0-2-3 ∷ []) (refl) ▸ done

  b10 : Chain (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K1 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ X4 ∷ Toff104 ∷ X4 ∷ CS14 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff104 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K1 ∷ CS14 ∷ [])
  b10 = at 7 4 (CS14 ∷ X4 ∷ Toff234 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff234 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ Toff234 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Toff104 ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ []) (lem-beta-T-at01102442 c4) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 4 (CS14 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CCZ123 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 4 (CS14 ∷ X4 ∷ Toff104 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff104 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ Toff104 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 4 (CS14 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CCZ123 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b11 : Chain (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ X4 ∷ Toff104 ∷ X4 ∷ CS14 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff104 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K1 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ X4 ∷ Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K1 ∷ CS14 ∷ [])
  b11 = at 4 4 (CS14 ∷ X4 ∷ Toff104 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff104 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ Toff104 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 9 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 6 4 (Bx1-0432 ∷ []) (sym (lem-beta-T-at01102442 c4)) ▸
       at 7 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 9 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b12 : Chain (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ X4 ∷ Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K1 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ CS14 ∷ [])
  b12 = at 10 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 6 5 (Sb1-0-43-2 ∷ []) (refl) ▸
       at 7 2 (K1 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ K1 ∷ []) (K1 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (K1 ∷ Sb1-0-43-2 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at01102442 c4) ▸
       at 5 2 (K1 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ K1 ∷ []) (K1 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b13 : Chain (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ [])
  b13 = at 14 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 1 (CS02⁻ ∷ []) (refl) ▸
       at 18 4 (CS14 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS02⁻ ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 20 1 (Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 15 4 (CS14 ∷ X4 ∷ Toff234 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff234 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ Toff234 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 1 (CS02 ∷ []) (refl) ▸
       at 12 4 (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS02 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b14 : Chain (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ []) (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Toff104 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ CS14 ∷ X4 ∷ Toff104 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ [])
  b14 = at 14 1 (Sb1-0-2-3 ∷ []) (refl) ▸
       at 9 4 (CS14 ∷ X4 ∷ Toff234 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff234 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ Toff234 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Toff104 ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ []) (lem-beta-T-at01102442 c4) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 4 (CS14 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CCZ123 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 4 (CS14 ∷ X4 ∷ Toff104 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff104 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ Toff104 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b15 : Chain (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Toff104 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ CS14 ∷ X4 ∷ Toff104 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ []) (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ X4 ∷ Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ [])
  b15 = at 9 4 (CS14 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CCZ123 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 6 4 (CS14 ∷ X4 ∷ Toff104 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff104 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ Toff104 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 10 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 11 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 8 4 (Bx1-0432 ∷ []) (sym (lem-beta-T-at01102442 c4)) ▸
       at 9 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 10 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b16 : Chain (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ X4 ∷ Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ []) (CK41 ∷ X4 ∷ Sb1-0-43-2 ∷ X4 ∷ [])
  b16 = at 11 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 12 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 8 5 (Sb1-0-43-2 ∷ []) (refl) ▸
       at 0 1 (ι1 ∷ []) (uₛ (iI) (iI ↑) Eq.refl) ▸
       at 0 7 (CK41 ∷ []) (pw0 c4 (ι1 ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ []) (CK41 ∷ []) tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | K4 @2442: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at2442 : Complete 4 → ⟪ (Sb0-1-43-2 ∷ K2 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at2442 c4 = run b0
  where
  b0 : Chain (Sb0-1-43-2 ∷ K2 ∷ []) (K2 ∷ Sb0-1-43-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ c4) ▸
       at 2 2 (K3 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ K2 ∷ []) (K3 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (K3 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at243243 c4) ▸
       at 0 2 (K2 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ K3 ∷ []) (K2 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | K4 @01102442: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at01102442 : Complete 4 → ⟪ (Sb1-0-43-2 ∷ K2 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at01102442 c4 = run b0
  where
  b0 : Chain (Sb1-0-43-2 ∷ K2 ∷ []) (K2 ∷ Sb1-0-43-2 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·43·2⟩ c4) ▸
       at 2 2 (K2 ∷ Sw01 ∷ []) (c₂ (Swap) (K)) ▸
       at 1 2 (K2 ∷ Sb0-1-43-2 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at2442 c4) ▸
       at 0 2 (K2 ∷ Sw01 ∷ []) (c₂ (Swap) (K)) ▸
       at 1 2 (Sb1-0-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·43·2⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- F4 CS03^0|K2^1: 131 steps
lem-F4-CS03ᵖ0∣K2ᵖ1 : Complete 4 → ⟪ (X4 ∷ Sb1-0-43-2 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ Sb1-0-43-2 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS03ᵖ0∣K2ᵖ1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (run b16))))))))))))))))
  where
  b0 : Chain (X4 ∷ Sb1-0-43-2 ∷ X4 ∷ CK42 ∷ []) (ι ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ [])
  b0 = at 3 1 (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ []) (lw1 c4 (CK42 ∷ []) (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (ι ∷ X4 ∷ []) (zc) ▸
       at 1 2 (ι ∷ Sb1-0-43-2 ∷ []) (zc) ▸
       at 0 2 (ι ∷ X4 ∷ []) (zc) ▸
       at 2 1 (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 3 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (ι ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ []) (ι ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ S4⁻ ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ [])
  b1 = at 12 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 1 (CS02⁻ ∷ []) (refl) ▸
       at 13 4 (S4⁻ ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) (lw3 c4 (X4 ∷ CS02⁻ ∷ X4 ∷ S4⁻ ∷ []) (S4⁻ ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 1 (Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 10 4 (S4⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff234 ∷ X4 ∷ S4⁻ ∷ []) (S4⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 1 (CS02 ∷ []) (refl) ▸
       at 7 4 (S4⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) (lw3 c4 (X4 ∷ CS02 ∷ X4 ∷ S4⁻ ∷ []) (S4⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 1 (Sb1-0-2-3 ∷ []) (refl) ▸ done

  b2 : Chain (ι ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ S4⁻ ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ []) (ι ∷ X4 ∷ Toff104 ∷ X4 ∷ S4⁻ ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff104 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ [])
  b2 = at 4 4 (S4⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff234 ∷ X4 ∷ S4⁻ ∷ []) (S4⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Toff104 ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ []) (lem-beta-T-at01102442 c4) ▸
       at 3 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 4 (S4⁻ ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CCZ123 ∷ X4 ∷ S4⁻ ∷ []) (S4⁻ ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 4 (S4⁻ ∷ X4 ∷ Toff104 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff104 ∷ X4 ∷ S4⁻ ∷ []) (S4⁻ ∷ X4 ∷ Toff104 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 4 (S4⁻ ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CCZ123 ∷ X4 ∷ S4⁻ ∷ []) (S4⁻ ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b3 : Chain (ι ∷ X4 ∷ Toff104 ∷ X4 ∷ S4⁻ ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff104 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ [])
  b3 = at 1 4 (S4⁻ ∷ X4 ∷ Toff104 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff104 ∷ X4 ∷ S4⁻ ∷ []) (S4⁻ ∷ X4 ∷ Toff104 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 3 4 (Bx1-0432 ∷ []) (sym (lem-beta-T-at01102442 c4)) ▸
       at 4 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b4 : Chain (ι ∷ S4⁻ ∷ X4 ∷ Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ [])
  b4 = at 7 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 3 5 (Sb1-0-43-2 ∷ []) (refl) ▸
       at 3 1 (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 1 (CS02⁻ ∷ []) (refl) ▸ done

  b5 : Chain (ι ∷ S4⁻ ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ Toff104 ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ X4 ∷ CS24 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ [])
  b5 = at 14 4 (CS24 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS02⁻ ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 1 (Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 11 4 (CS24 ∷ X4 ∷ Toff234 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff234 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ Toff234 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 1 (CS02 ∷ []) (refl) ▸
       at 8 4 (CS24 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS02 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 1 (Sb1-0-2-3 ∷ []) (refl) ▸
       at 5 4 (CS24 ∷ X4 ∷ Toff234 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff234 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ Toff234 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Toff104 ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ []) (lem-beta-T-at01102442 c4) ▸ done

  b6 : Chain (ι ∷ S4⁻ ∷ X4 ∷ Toff104 ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ X4 ∷ CS24 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ []) (ι ∷ S4⁻ ∷ CS24 ∷ X4 ∷ Toff104 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff104 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ [])
  b6 = at 4 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 4 (CS24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CCZ123 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 4 (CS24 ∷ X4 ∷ Toff104 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ Toff104 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ Toff104 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 4 (CS24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CCZ123 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (CS24 ∷ X4 ∷ Toff104 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ Toff104 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ Toff104 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b7 : Chain (ι ∷ S4⁻ ∷ CS24 ∷ X4 ∷ Toff104 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff104 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ []) (ι ∷ S4⁻ ∷ CS24 ∷ X4 ∷ Sb1-0-43-2 ∷ X4 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ [])
  b7 = at 6 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 4 4 (Bx1-0432 ∷ []) (sym (lem-beta-T-at01102442 c4)) ▸
       at 5 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 4 5 (Sb1-0-43-2 ∷ []) (refl) ▸ done

  b8 : Chain (ι ∷ S4⁻ ∷ CS24 ∷ X4 ∷ Sb1-0-43-2 ∷ X4 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ []) (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ CS24 ∷ K2 ∷ CS24 ∷ [])
  b8 = at 5 2 (K2 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ K2 ∷ []) (K2 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (K2 ∷ Sb1-0-43-2 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at01102442 c4) ▸
       at 3 2 (K2 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ K2 ∷ []) (K2 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b9 : Chain (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ CS24 ∷ K2 ∷ CS24 ∷ []) (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ CS24 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K2 ∷ CS24 ∷ [])
  b9 = at 17 1 (CS02⁻ ∷ []) (refl) ▸
       at 16 4 (CS24 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS02⁻ ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 18 1 (Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 13 4 (CS24 ∷ X4 ∷ Toff234 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff234 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ Toff234 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 1 (CS02 ∷ []) (refl) ▸
       at 10 4 (CS24 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS02 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 1 (Sb1-0-2-3 ∷ []) (refl) ▸
       at 7 4 (CS24 ∷ X4 ∷ Toff234 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff234 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ Toff234 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b10 : Chain (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ CS24 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K2 ∷ CS24 ∷ []) (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ X4 ∷ Toff104 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff104 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K2 ∷ CS24 ∷ [])
  b10 = at 5 1 (Toff104 ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ []) (lem-beta-T-at01102442 c4) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 4 (CS24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CCZ123 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 4 (CS24 ∷ X4 ∷ Toff104 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ Toff104 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ Toff104 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 4 (CS24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CCZ123 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 4 (CS24 ∷ X4 ∷ Toff104 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ Toff104 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ Toff104 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b11 : Chain (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ X4 ∷ Toff104 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff104 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K2 ∷ CS24 ∷ []) (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ X4 ∷ Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K2 ∷ CS24 ∷ [])
  b11 = at 7 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 9 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 6 4 (Bx1-0432 ∷ []) (sym (lem-beta-T-at01102442 c4)) ▸
       at 7 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 9 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 10 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b12 : Chain (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ X4 ∷ Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K2 ∷ CS24 ∷ []) (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ CS24 ∷ [])
  b12 = at 6 5 (Sb1-0-43-2 ∷ []) (refl) ▸
       at 7 2 (K2 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ K2 ∷ []) (K2 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (K2 ∷ Sb1-0-43-2 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at01102442 c4) ▸
       at 5 2 (K2 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ K2 ∷ []) (K2 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b13 : Chain (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ CS24 ∷ []) (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ [])
  b13 = at 17 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 1 (CS02⁻ ∷ []) (refl) ▸
       at 18 4 (CS24 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS02⁻ ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 20 1 (Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 15 4 (CS24 ∷ X4 ∷ Toff234 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff234 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ Toff234 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 1 (CS02 ∷ []) (refl) ▸
       at 12 4 (CS24 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS02 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 1 (Sb1-0-2-3 ∷ []) (refl) ▸ done

  b14 : Chain (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ []) (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ X4 ∷ Toff104 ∷ X4 ∷ CS24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff104 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ [])
  b14 = at 9 4 (CS24 ∷ X4 ∷ Toff234 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff234 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ Toff234 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Toff104 ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ []) (lem-beta-T-at01102442 c4) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 4 (CS24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CCZ123 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 4 (CS24 ∷ X4 ∷ Toff104 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ Toff104 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ Toff104 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 4 (CS24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CCZ123 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b15 : Chain (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ X4 ∷ Toff104 ∷ X4 ∷ CS24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff104 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ []) (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ X4 ∷ Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ [])
  b15 = at 6 4 (CS24 ∷ X4 ∷ Toff104 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ Toff104 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ Toff104 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 10 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 11 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 8 4 (Bx1-0432 ∷ []) (sym (lem-beta-T-at01102442 c4)) ▸
       at 9 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 10 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 11 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b16 : Chain (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ X4 ∷ Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ []) (CK42 ∷ X4 ∷ Sb1-0-43-2 ∷ X4 ∷ [])
  b16 = at 12 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 8 5 (Sb1-0-43-2 ∷ []) (refl) ▸
       at 0 7 (CK42 ∷ []) (lw1 c4 (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ []) (CK42 ∷ []) tt tt Eq.refl) ▸ done


-- F4 CS03^0|K3^1: 185 steps
lem-F4-CS03ᵖ0∣K3ᵖ1 : Complete 4 → ⟪ (X4 ∷ Sb1-0-43-2 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ Sb1-0-43-2 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS03ᵖ0∣K3ᵖ1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (run b23)))))))))))))))))))))))
  where
  b0 : Chain (X4 ∷ Sb1-0-43-2 ∷ X4 ∷ CK43 ∷ []) (ι ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ [])
  b0 = at 3 1 (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ []) (lw1 c4 (CK43 ∷ []) (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (ι ∷ X4 ∷ []) (zc) ▸
       at 1 2 (ι ∷ Sb1-0-43-2 ∷ []) (zc) ▸
       at 0 2 (ι ∷ X4 ∷ []) (zc) ▸
       at 2 1 (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 3 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (ι ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ []) (ι ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ S4⁻ ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ [])
  b1 = at 12 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 1 (CS02⁻ ∷ []) (refl) ▸
       at 13 4 (S4⁻ ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) (lw3 c4 (X4 ∷ CS02⁻ ∷ X4 ∷ S4⁻ ∷ []) (S4⁻ ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 1 (Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 10 4 (S4⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff234 ∷ X4 ∷ S4⁻ ∷ []) (S4⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 1 (CS02 ∷ []) (refl) ▸
       at 7 4 (S4⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) (lw3 c4 (X4 ∷ CS02 ∷ X4 ∷ S4⁻ ∷ []) (S4⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 1 (Sb1-0-2-3 ∷ []) (refl) ▸ done

  b2 : Chain (ι ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ S4⁻ ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ []) (ι ∷ X4 ∷ Toff104 ∷ X4 ∷ S4⁻ ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff104 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ [])
  b2 = at 4 4 (S4⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff234 ∷ X4 ∷ S4⁻ ∷ []) (S4⁻ ∷ X4 ∷ Toff234 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Toff104 ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ []) (lem-beta-T-at01102442 c4) ▸
       at 3 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 4 (S4⁻ ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CCZ123 ∷ X4 ∷ S4⁻ ∷ []) (S4⁻ ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 4 (S4⁻ ∷ X4 ∷ Toff104 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff104 ∷ X4 ∷ S4⁻ ∷ []) (S4⁻ ∷ X4 ∷ Toff104 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 4 (S4⁻ ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CCZ123 ∷ X4 ∷ S4⁻ ∷ []) (S4⁻ ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b3 : Chain (ι ∷ X4 ∷ Toff104 ∷ X4 ∷ S4⁻ ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff104 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ [])
  b3 = at 1 4 (S4⁻ ∷ X4 ∷ Toff104 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff104 ∷ X4 ∷ S4⁻ ∷ []) (S4⁻ ∷ X4 ∷ Toff104 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 3 4 (Bx1-0432 ∷ []) (sym (lem-beta-T-at01102442 c4)) ▸
       at 4 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b4 : Chain (ι ∷ S4⁻ ∷ X4 ∷ Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ [])
  b4 = at 7 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 3 5 (Sb1-0-43-2 ∷ []) (refl) ▸
       at 3 1 (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 1 (CS02⁻ ∷ []) (refl) ▸ done

  b5 : Chain (ι ∷ S4⁻ ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ Toff104 ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ X4 ∷ CS34 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ [])
  b5 = at 14 4 (CS34 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS02⁻ ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 1 (Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 11 4 (CS34 ∷ X4 ∷ Toff234 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff234 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ Toff234 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 1 (CS02 ∷ []) (refl) ▸
       at 8 4 (CS34 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS02 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 1 (Sb1-0-2-3 ∷ []) (refl) ▸
       at 5 4 (CS34 ∷ X4 ∷ Toff234 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff234 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ Toff234 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Toff104 ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ []) (lem-beta-T-at01102442 c4) ▸ done

  b6 : Chain (ι ∷ S4⁻ ∷ X4 ∷ Toff104 ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ X4 ∷ CS34 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ []) (ι ∷ S4⁻ ∷ CS34 ∷ X4 ∷ Toff104 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff104 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ [])
  b6 = at 4 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 4 (CS34 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CCZ123 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 4 (CS34 ∷ X4 ∷ Toff104 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff104 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ Toff104 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 4 (CS34 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CCZ123 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (CS34 ∷ X4 ∷ Toff104 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff104 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ Toff104 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b7 : Chain (ι ∷ S4⁻ ∷ CS34 ∷ X4 ∷ Toff104 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff104 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ []) (ι ∷ S4⁻ ∷ CS34 ∷ X4 ∷ Sb1-0-43-2 ∷ X4 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ [])
  b7 = at 6 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 4 4 (Bx1-0432 ∷ []) (sym (lem-beta-T-at01102442 c4)) ▸
       at 5 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 4 5 (Sb1-0-43-2 ∷ []) (refl) ▸ done

  b8 : Chain (ι ∷ S4⁻ ∷ CS34 ∷ X4 ∷ Sb1-0-43-2 ∷ X4 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ []) (ι ∷ S4⁻ ∷ CS34 ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CS34 ∷ K3 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ CS34 ∷ [])
  b8 = at 4 1 (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 1 (CS02⁻ ∷ []) (refl) ▸
       at 15 6 (K3 ∷ CS34 ∷ K3 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS02⁻ ∷ X4 ∷ K3 ∷ CS34 ∷ K3 ∷ []) (K3 ∷ CS34 ∷ K3 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 1 (Sb⁻1-0-2-3 ∷ []) (refl) ▸ done

  b9 : Chain (ι ∷ S4⁻ ∷ CS34 ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CS34 ∷ K3 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ CS34 ∷ []) (ι ∷ S4⁻ ∷ CS34 ∷ X4 ∷ Toff102 ∷ CCZ134 ∷ Toff102 ∷ CCZ134 ∷ X4 ∷ K3 ∷ CS34 ∷ K3 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ CS34 ∷ [])
  b9 = at 12 6 (K3 ∷ CS34 ∷ K3 ∷ X4 ∷ Toff234 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CS34 ∷ K3 ∷ []) (K3 ∷ CS34 ∷ K3 ∷ X4 ∷ Toff234 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 1 (CS02 ∷ []) (refl) ▸
       at 9 6 (K3 ∷ CS34 ∷ K3 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS02 ∷ X4 ∷ K3 ∷ CS34 ∷ K3 ∷ []) (K3 ∷ CS34 ∷ K3 ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 1 (Sb1-0-2-3 ∷ []) (refl) ▸
       at 6 6 (K3 ∷ CS34 ∷ K3 ∷ X4 ∷ Toff234 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff234 ∷ X4 ∷ K3 ∷ CS34 ∷ K3 ∷ []) (K3 ∷ CS34 ∷ K3 ∷ X4 ∷ Toff234 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx1-0423 ∷ []) (lem-sym34-at01102442 c4) ▸
       at 4 1 (Bx1-0243 ∷ []) (lem-sym23-at0110243243 c4) ▸
       at 4 1 (Toff102 ∷ CCZ134 ∷ Toff102 ∷ CCZ134 ∷ []) (lem-beta-T-at01103443 c4) ▸ done

  b10 : Chain (ι ∷ S4⁻ ∷ CS34 ∷ X4 ∷ Toff102 ∷ CCZ134 ∷ Toff102 ∷ CCZ134 ∷ X4 ∷ K3 ∷ CS34 ∷ K3 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ CS34 ∷ []) (ι ∷ S4⁻ ∷ CS34 ∷ X4 ∷ Toff102 ∷ X4 ∷ X4 ∷ CCZ134 ∷ X4 ∷ K3 ∷ X4 ∷ K1 ∷ CCZ012 ∷ K1⁻ ∷ X4 ∷ CS34 ∷ K3 ∷ X4 ∷ CCZ134 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ CS34 ∷ [])
  b10 = at 5 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 6 (K3 ∷ CS34 ∷ K3 ∷ X4 ∷ CCZ134 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CCZ134 ∷ X4 ∷ K3 ∷ CS34 ∷ K3 ∷ []) (K3 ∷ CS34 ∷ K3 ∷ X4 ∷ CCZ134 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 10 2 (K3 ∷ Toff102 ∷ []) (c₃ (K ↑ • CCZ • K ↑ • iI) (K)) ▸
       at 9 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 11 1 (K1 ∷ CCZ012 ∷ K1⁻ ∷ []) (lw4 c4 (Toff102 ∷ []) (K1 ∷ CCZ012 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸ done

  b11 : Chain (ι ∷ S4⁻ ∷ CS34 ∷ X4 ∷ Toff102 ∷ X4 ∷ X4 ∷ CCZ134 ∷ X4 ∷ K3 ∷ X4 ∷ K1 ∷ CCZ012 ∷ K1⁻ ∷ X4 ∷ CS34 ∷ K3 ∷ X4 ∷ CCZ134 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ CS34 ∷ []) (ι ∷ S4⁻ ∷ CS34 ∷ X4 ∷ Toff102 ∷ X4 ∷ X4 ∷ CCZ134 ∷ X4 ∷ K3 ∷ X4 ∷ K1 ∷ X4 ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ CX02 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ X4 ∷ CX02 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ CS34 ∷ X4 ∷ K1⁻ ∷ X4 ∷ K3 ∷ X4 ∷ CCZ134 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ CS34 ∷ [])
  b11 = at 12 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 4 (CS34 ∷ X4 ∷ K1⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ K1⁻ ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ K1⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 1 (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 21 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 24 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b12 : Chain (ι ∷ S4⁻ ∷ CS34 ∷ X4 ∷ Toff102 ∷ X4 ∷ X4 ∷ CCZ134 ∷ X4 ∷ K3 ∷ X4 ∷ K1 ∷ X4 ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ CX02 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ X4 ∷ CX02 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ CS34 ∷ X4 ∷ K1⁻ ∷ X4 ∷ K3 ∷ X4 ∷ CCZ134 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ CS34 ∷ []) (ι ∷ S4⁻ ∷ CS34 ∷ X4 ∷ Toff102 ∷ X4 ∷ X4 ∷ CCZ134 ∷ X4 ∷ K3 ∷ X4 ∷ K1 ∷ X4 ∷ CS34 ∷ X4 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ K1⁻ ∷ X4 ∷ K3 ∷ X4 ∷ CCZ134 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ CS34 ∷ [])
  b12 = at 25 4 (CS34 ∷ X4 ∷ CS01 ∷ X4 ∷ []) (lw2 c4 (X4 ∷ CS01 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS01 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 22 4 (CS34 ∷ X4 ∷ CX02 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CX02 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CX02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 4 (CS34 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12⁻ ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 4 (CS34 ∷ X4 ∷ CX02 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CX02 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CX02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 4 (CS34 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS12 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 17 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 18 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b13 : Chain (ι ∷ S4⁻ ∷ CS34 ∷ X4 ∷ Toff102 ∷ X4 ∷ X4 ∷ CCZ134 ∷ X4 ∷ K3 ∷ X4 ∷ K1 ∷ X4 ∷ CS34 ∷ X4 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ K1⁻ ∷ X4 ∷ K3 ∷ X4 ∷ CCZ134 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ CS34 ∷ []) (ι ∷ S4⁻ ∷ CS34 ∷ X4 ∷ Toff102 ∷ X4 ∷ X4 ∷ CCZ134 ∷ X4 ∷ K3 ∷ CS34 ∷ X4 ∷ K3 ∷ Toff102 ∷ X4 ∷ X4 ∷ CCZ134 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ CS34 ∷ [])
  b13 = at 19 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 15 5 (CCZ012 ∷ []) (lw4 c4 (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 10 4 (CS34 ∷ X4 ∷ K1 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ K1 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ K1 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 14 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 12 3 (Toff102 ∷ []) (lw4 c4 (K1 ∷ CCZ012 ∷ K1⁻ ∷ []) (Toff102 ∷ []) tt tt Eq.refl) ▸
       at 13 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 12 2 (K3 ∷ Toff102 ∷ []) (c₃ (K ↑ • CCZ • K ↑ • iI) (K)) ▸ done

  b14 : Chain (ι ∷ S4⁻ ∷ CS34 ∷ X4 ∷ Toff102 ∷ X4 ∷ X4 ∷ CCZ134 ∷ X4 ∷ K3 ∷ CS34 ∷ X4 ∷ K3 ∷ Toff102 ∷ X4 ∷ X4 ∷ CCZ134 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ CS34 ∷ []) (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ X4 ∷ K1 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ K1⁻ ∷ X4 ∷ CS34 ∷ K3 ∷ X4 ∷ CCZ134 ∷ X4 ∷ X4 ∷ Toff102 ∷ X4 ∷ X4 ∷ CCZ134 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ CS34 ∷ [])
  b14 = at 11 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 6 6 (K3 ∷ CS34 ∷ K3 ∷ X4 ∷ CCZ134 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CCZ134 ∷ X4 ∷ K3 ∷ CS34 ∷ K3 ∷ []) (K3 ∷ CS34 ∷ K3 ∷ X4 ∷ CCZ134 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 4 2 (K3 ∷ Toff102 ∷ []) (c₃ (K ↑ • CCZ • K ↑ • iI) (K)) ▸
       at 3 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 5 1 (K1 ∷ CCZ012 ∷ K1⁻ ∷ []) (lw4 c4 (Toff102 ∷ []) (K1 ∷ CCZ012 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b15 : Chain (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ X4 ∷ K1 ∷ X4 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ K1⁻ ∷ X4 ∷ CS34 ∷ K3 ∷ X4 ∷ CCZ134 ∷ X4 ∷ X4 ∷ Toff102 ∷ X4 ∷ X4 ∷ CCZ134 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ CS34 ∷ []) (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ X4 ∷ K1 ∷ X4 ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ CX02 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ CS34 ∷ X4 ∷ CX02 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ K1⁻ ∷ X4 ∷ K3 ∷ X4 ∷ CCZ134 ∷ X4 ∷ X4 ∷ Toff102 ∷ X4 ∷ X4 ∷ CCZ134 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ CS34 ∷ [])
  b15 = at 10 4 (CS34 ∷ X4 ∷ K1⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ K1⁻ ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ K1⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 1 (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 4 (CS34 ∷ X4 ∷ CS01 ∷ X4 ∷ []) (lw2 c4 (X4 ∷ CS01 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS01 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 16 4 (CS34 ∷ X4 ∷ CX02 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CX02 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CX02 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b16 : Chain (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ X4 ∷ K1 ∷ X4 ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ CX02 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ CS34 ∷ X4 ∷ CX02 ∷ X4 ∷ X4 ∷ CS01 ∷ X4 ∷ X4 ∷ K1⁻ ∷ X4 ∷ K3 ∷ X4 ∷ CCZ134 ∷ X4 ∷ X4 ∷ Toff102 ∷ X4 ∷ X4 ∷ CCZ134 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ CS34 ∷ []) (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ X4 ∷ K1 ∷ X4 ∷ CS34 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ K1⁻ ∷ X4 ∷ K3 ∷ X4 ∷ CCZ134 ∷ X4 ∷ X4 ∷ Toff102 ∷ X4 ∷ X4 ∷ CCZ134 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ CS34 ∷ [])
  b16 = at 13 4 (CS34 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12⁻ ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 4 (CS34 ∷ X4 ∷ CX02 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CX02 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CX02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 4 (CS34 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS12 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 10 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 11 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 12 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 13 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 9 5 (CCZ012 ∷ []) (lw4 c4 (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸ done

  b17 : Chain (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ X4 ∷ K1 ∷ X4 ∷ CS34 ∷ X4 ∷ CCZ012 ∷ X4 ∷ X4 ∷ K1⁻ ∷ X4 ∷ K3 ∷ X4 ∷ CCZ134 ∷ X4 ∷ X4 ∷ Toff102 ∷ X4 ∷ X4 ∷ CCZ134 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ CS34 ∷ []) (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ X4 ∷ Toff102 ∷ CCZ134 ∷ X4 ∷ X4 ∷ Toff102 ∷ X4 ∷ X4 ∷ CCZ134 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ CS34 ∷ [])
  b17 = at 4 4 (CS34 ∷ X4 ∷ K1 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ K1 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ K1 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 6 3 (Toff102 ∷ []) (lw4 c4 (K1 ∷ CCZ012 ∷ K1⁻ ∷ []) (Toff102 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 6 2 (K3 ∷ Toff102 ∷ []) (c₃ (K ↑ • CCZ • K ↑ • iI) (K)) ▸
       at 5 2 (K3 ∷ X4 ∷ []) (sym (c₄ (K ↑ ↑ ↑) (X))) ▸
       at 8 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b18 : Chain (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ X4 ∷ Toff102 ∷ CCZ134 ∷ X4 ∷ X4 ∷ Toff102 ∷ X4 ∷ X4 ∷ CCZ134 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ CS34 ∷ []) (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ X4 ∷ Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ CS34 ∷ [])
  b18 = at 9 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 10 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 7 4 (Bx1-0243 ∷ []) (sym (lem-beta-T-at01103443 c4)) ▸
       at 7 1 (Bx1-0423 ∷ []) (lem-sym23-at01103443 c4) ▸
       at 7 1 (Bx1-0432 ∷ []) (lem-sym34-at0110243243 c4) ▸
       at 8 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 9 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 10 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b19 : Chain (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ X4 ∷ Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ CS34 ∷ []) (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ CS34 ∷ [])
  b19 = at 11 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 7 5 (Sb1-0-43-2 ∷ []) (refl) ▸
       at 7 1 (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 17 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 19 1 (CS02⁻ ∷ []) (refl) ▸ done

  b20 : Chain (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ CS34 ∷ []) (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ X4 ∷ Toff104 ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ X4 ∷ CS34 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ [])
  b20 = at 18 4 (CS34 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS02⁻ ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 20 1 (Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 15 4 (CS34 ∷ X4 ∷ Toff234 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff234 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ Toff234 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 1 (CS02 ∷ []) (refl) ▸
       at 12 4 (CS34 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS02 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS02 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 1 (Sb1-0-2-3 ∷ []) (refl) ▸
       at 9 4 (CS34 ∷ X4 ∷ Toff234 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff234 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ Toff234 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Toff104 ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ []) (lem-beta-T-at01102442 c4) ▸ done

  b21 : Chain (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ X4 ∷ Toff104 ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ X4 ∷ CS34 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ []) (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ X4 ∷ Toff104 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff104 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ [])
  b21 = at 8 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 15 4 (CS34 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CCZ123 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 12 4 (CS34 ∷ X4 ∷ Toff104 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff104 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ Toff104 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 4 (CS34 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CCZ123 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 6 4 (CS34 ∷ X4 ∷ Toff104 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ Toff104 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ Toff104 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b22 : Chain (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ X4 ∷ Toff104 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff104 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb1-0-2-3 ∷ X4 ∷ X4 ∷ Toff234 ∷ X4 ∷ X4 ∷ Sb⁻1-0-2-3 ∷ X4 ∷ []) (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ X4 ∷ Sb1-0-43-2 ∷ X4 ∷ [])
  b22 = at 10 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 11 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 8 4 (Bx1-0432 ∷ []) (sym (lem-beta-T-at01102442 c4)) ▸
       at 9 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 10 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 11 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 12 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 8 5 (Sb1-0-43-2 ∷ []) (refl) ▸ done

  b23 : Chain (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ X4 ∷ Sb1-0-43-2 ∷ X4 ∷ []) (CK43 ∷ X4 ∷ Sb1-0-43-2 ∷ X4 ∷ [])
  b23 = at 0 7 (CK43 ∷ []) (lw1 c4 (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ []) (CK43 ∷ []) tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CCZ413 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ413-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ413-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 1 2 (CCZ134 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ413 c4) ▸
       at 0 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | TOFF412: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF412 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF412 c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ Toff412 ∷ []) (Toff412 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 1 1 (K4 ∷ CCZ124 ∷ K4⁻ ∷ []) (lw0 c4 (Toff412 ∷ []) (K4 ∷ CCZ124 ∷ K4⁻ ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (K4 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at2332 c4) ▸
       at 1 2 (CCZ124 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ413-at2332 c4) ▸
       at 2 2 (K4⁻ ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd4-at2332 c4) ▸
       at 3 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 3 (Toff412 ∷ []) (lw0 c4 (K4 ∷ CCZ124 ∷ K4⁻ ∷ []) (Toff412 ∷ []) tt tt Eq.refl) ▸ done


-- auto CSd01 | BOX(1;0234): 5 steps
lem-auto-CSd01-∣-BOX⟨1·0234⟩ : Complete 4 → ⟪ (CS01⁻ ∷ Bx1-0234 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0234 ∷ CS01⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨1·0234⟩ c4 = run b0
  where
  b0 : Chain (CS01⁻ ∷ Bx1-0234 ∷ []) (Bx1-0234 ∷ CS01⁻ ∷ [])
  b0 = at 0 1 (CS01⁻ ∷ []) (lw4 c4 (CS01⁻ ∷ []) (CS01⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx1-2034 ∷ []) (lem-sym12-at0110 c4) ▸
       at 0 2 (Bx1-2034 ∷ CS01⁻ ∷ []) (lem-CS20-beta-ci-at011220 c4) ▸
       at 0 1 (Bx1-0234 ∷ []) (lem-sym12-at011220 c4) ▸
       at 1 1 (CS01⁻ ∷ []) (lw4 c4 (CS01⁻ ∷ []) (CS01⁻ ∷ []) tt tt Eq.refl) ▸ done


-- auto CSd01 | BOX(1;0234) @2332: 7 steps
lem-auto-CSd01-∣-BOX⟨1·0234⟩-at2332 : Complete 4 → ⟪ (CS01⁻ ∷ Bx1-0324 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0324 ∷ CS01⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨1·0234⟩-at2332 c4 = run b0
  where
  b0 : Chain (CS01⁻ ∷ Bx1-0324 ∷ []) (Bx1-0324 ∷ CS01⁻ ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS01⁻ ∷ Sw23 ∷ []) (sym (c₂ (CS • CS • CS) (Swap))) ▸
       at 2 2 (Bx1-0234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0324⟩ c4) ▸
       at 1 2 (Bx1-0234 ∷ CS01⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨1·0234⟩ c4) ▸
       at 0 2 (Bx1-0324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0234⟩ c4) ▸
       at 1 2 (CS01⁻ ∷ Sw23 ∷ []) (sym (c₂ (CS • CS • CS) (Swap))) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CSd01 | BOX(1;0234) @243243: 7 steps
lem-auto-CSd01-∣-BOX⟨1·0234⟩-at243243 : Complete 4 → ⟪ (CS01⁻ ∷ Bx1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ CS01⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨1·0234⟩-at243243 c4 = run b0
  where
  b0 : Chain (CS01⁻ ∷ Bx1-0423 ∷ []) (Bx1-0423 ∷ CS01⁻ ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS01⁻ ∷ Sw34 ∷ []) (sym (c₂ (CS • CS • CS) (Swap ↑))) ▸
       at 2 2 (Bx1-0324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·0423⟩ c4) ▸
       at 1 2 (Bx1-0324 ∷ CS01⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨1·0234⟩-at2332 c4) ▸
       at 0 2 (Bx1-0423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·0324⟩ c4) ▸
       at 1 2 (CS01⁻ ∷ Sw34 ∷ []) (sym (c₂ (CS • CS • CS) (Swap ↑))) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


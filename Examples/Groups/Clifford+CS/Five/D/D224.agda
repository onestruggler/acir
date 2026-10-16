{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D224 where

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
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-BOXd-BOX ; lem-CS20-beta-ci ; lem-K0-pass-ci ; lem-beta-T-at2332 ; lem-sym12)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-sym12-at1221)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-AX-SB ; lem-BOXd-BOX-at2332 ; lem-CS20-beta-c-at1221)
open import Examples.Groups.Clifford+CS.Five.D.D008 using (lem-SBsymd-at0113203442)
open import Examples.Groups.Clifford+CS.Five.D.D010 using (lem-sym23-at0220 ; lem-sym23-at022330)
open import Examples.Groups.Clifford+CS.Five.D.D079 using (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS02)
open import Examples.Groups.Clifford+CS.Five.D.D080 using (lem-CS12-beta-at0220 ; lem-auto-CS01-∣-TOFF234-at243243 ; lem-sym34-at022330 ; lem-sym34-at02233440)
open import Examples.Groups.Clifford+CS.Five.D.D081 using (lem-auto-CX01-∣-TOFF234-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D222 using (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS21-at2332 ; lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS41-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D223 using (lem-BOXd-BOX-at0210233441 ; lem-F0d-at14213243 ; lem-auto-CS01-∣-BOXd⟨2·0341⟩ ; lem-auto-CX01-∣-BOXd⟨1·0234⟩)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-CCZ023)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-1-CCZ013)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-2-CCZ124 ; lem-nat-2-CCZ134)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-3-CCZ123 ; lem-nat-3-CCZ124)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-2-CS02 ; lem-nat-2-CSd02)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-0-BOX⟨2·0341⟩ ; lem-nat-3-SBOX⟨1·0·2·4⟩ ; lem-nat-3-SBOXd⟨1·0·2·4⟩)
open import Examples.Groups.Clifford+CS.Five.D.R018 using (lem-nat-2-SBOXd⟨0·1·23·4⟩ ; lem-nat-2-SBOXd⟨0·1·32·4⟩)
open import Examples.Groups.Clifford+CS.Five.D.R019 using (lem-nat-2-CS03 ; lem-nat-2-CSd03)
open import Examples.Groups.Clifford+CS.Five.D.R020 using (lem-nat-2-SBOX⟨1·0·3·4⟩ ; lem-nat-2-SBOXd⟨1·0·3·4⟩)
open import Examples.Groups.Clifford+CS.Five.D.R021 using (lem-nat-1-SBOX⟨0·1·2·3⟩ ; lem-nat-1-SBOX⟨0·2·1·3⟩ ; lem-nat-1-SBOXd⟨0·1·2·3⟩ ; lem-nat-1-SBOXd⟨0·2·1·3⟩)
open import Examples.Groups.Clifford+CS.Five.D.R022 using (lem-nat-0-SBOXd⟨0·1·42·3⟩ ; lem-nat-0-SBOXd⟨1·0·42·3⟩ ; lem-nat-1-SBOXd⟨1·0·42·3⟩ ; lem-nat-1-SBOXd⟨2·0·41·3⟩ ; lem-nat-2-SBOX⟨1·0·2·4⟩ ; lem-nat-2-SBOXd⟨1·0·2·4⟩ ; lem-nat-3-SBOX⟨1·0·2·3⟩ ; lem-nat-3-SBOXd⟨0·1·32·4⟩ ; lem-nat-3-SBOXd⟨0·1·42·3⟩ ; lem-nat-3-SBOXd⟨1·0·2·3⟩)
open import Examples.Groups.Clifford+CS.Five.D.R033 using (lem-nat-0-SBOX⟨0·1·2·3⟩ ; lem-nat-0-SBOX⟨1·0·2·3⟩ ; lem-nat-0-SBOXd⟨0·1·2·3⟩ ; lem-nat-0-SBOXd⟨1·0·2·3⟩)
open import Examples.Groups.Clifford+CS.Five.D.R042 using (lem-comm-CCZ024-CSd13)
open import Examples.Groups.Clifford+CS.Five.D.R043 using (lem-nat-0-BOXd⟨2·1340⟩ ; lem-nat-0-SBOXd⟨0·1·34·2⟩ ; lem-nat-0-SBOXd⟨1·2·34·0⟩ ; lem-nat-0-SBOXd⟨2·0·34·1⟩ ; lem-nat-1-BOXd⟨0·1342⟩ ; lem-nat-1-BOXd⟨0·2341⟩ ; lem-nat-1-SBOXd⟨0·2·34·1⟩ ; lem-nat-1-SBOXd⟨2·1·34·0⟩ ; lem-nat-2-BOXd⟨0·1243⟩ ; lem-nat-2-BOXd⟨0·1342⟩ ; lem-nat-3-BOXd⟨0·1234⟩ ; lem-nat-3-BOXd⟨0·1243⟩ ; lem-nat-3-SBOX⟨0·2·34·1⟩ ; lem-nat-3-SBOX⟨0·2·43·1⟩)
-- auto CS01 | SBOXd(2;0;34;1): 9 steps
lem-auto-CS01-∣-SBOXd⟨2·0·34·1⟩ : Complete 4 → ⟪ (CS01 ∷ Sb⁻2-0-34-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-34-1 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOXd⟨2·0·34·1⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS01 ∷ Sb⁻2-0-34-1 ∷ []) (Sb2-0-1-4 ∷ Toff134 ∷ Sb⁻2-0-1-4 ∷ Toff134 ∷ Bx⁻2-0341 ∷ CS01 ∷ [])
  b0 = at 1 1 (Sb2-0-1-4 ∷ Toff134 ∷ Sb⁻2-0-1-4 ∷ Toff134 ∷ Bx⁻2-0341 ∷ []) (refl) ▸
       at 1 1 (CS01 ∷ []) (refl) ▸
       at 0 2 (CS01 ∷ CS01 ∷ []) (lw4 c4 (CS01 ∷ CS01 ∷ []) (CS01 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb2-0-1-4 ∷ []) (refl) ▸
       at 3 1 (CS01⁻ ∷ []) (refl) ▸
       at 1 4 (Toff134 ∷ CS01⁻ ∷ Toff134 ∷ CS01 ∷ []) (pw2 c4 (CS01 ∷ Toff134 ∷ CS01⁻ ∷ Toff134 ∷ []) (Toff134 ∷ CS01⁻ ∷ Toff134 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb⁻2-0-1-4 ∷ []) (refl) ▸
       at 4 2 (Bx⁻2-0341 ∷ CS01 ∷ []) (lem-auto-CS01-∣-BOXd⟨2·0341⟩ c4) ▸ done

  b1 : Chain (Sb2-0-1-4 ∷ Toff134 ∷ Sb⁻2-0-1-4 ∷ Toff134 ∷ Bx⁻2-0341 ∷ CS01 ∷ []) (Sb⁻2-0-34-1 ∷ CS01 ∷ [])
  b1 = at 0 5 (Sb⁻2-0-34-1 ∷ []) (refl) ▸ done


-- auto CX01 | SBOXd(1;0;23;4): 11 steps
lem-auto-CX01-∣-SBOXd⟨1·0·23·4⟩ : Complete 4 → ⟪ (CX01 ∷ Sb⁻1-0-23-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-23-4 ∷ CX01 ∷ []) ⟫ʷ
lem-auto-CX01-∣-SBOXd⟨1·0·23·4⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX01 ∷ Sb⁻1-0-23-4 ∷ []) (Sb1-0-4-3 ∷ Toff423 ∷ Sb⁻1-0-4-3 ∷ CX01 ∷ Toff423 ∷ Bx⁻1-0234 ∷ [])
  b0 = at 1 1 (Sb1-0-4-3 ∷ Toff423 ∷ Sb⁻1-0-4-3 ∷ Toff423 ∷ Bx⁻1-0234 ∷ []) (refl) ▸
       at 1 1 (CS04 ∷ []) (refl) ▸
       at 0 2 (CS04 ∷ CX01 ∷ []) (pw2 c4 (CX01 ∷ CS04 ∷ []) (CS04 ∷ CX01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb1-0-4-3 ∷ []) (refl) ▸
       at 1 2 (Toff423 ∷ CX01 ∷ []) (lem-auto-CX01-∣-TOFF234-at243243 c4) ▸
       at 3 1 (CS04⁻ ∷ []) (refl) ▸
       at 2 2 (CS04⁻ ∷ CX01 ∷ []) (pw2 c4 (CX01 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ CX01 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb⁻1-0-4-3 ∷ []) (refl) ▸ done

  b1 : Chain (Sb1-0-4-3 ∷ Toff423 ∷ Sb⁻1-0-4-3 ∷ CX01 ∷ Toff423 ∷ Bx⁻1-0234 ∷ []) (Sb⁻1-0-23-4 ∷ CX01 ∷ [])
  b1 = at 3 2 (Toff423 ∷ CX01 ∷ []) (lem-auto-CX01-∣-TOFF234-at243243 c4) ▸
       at 4 2 (Bx⁻1-0234 ∷ CX01 ∷ []) (lem-auto-CX01-∣-BOXd⟨1·0234⟩ c4) ▸
       at 0 5 (Sb⁻1-0-23-4 ∷ []) (refl) ▸ done


-- auto CS01 | BOXd(0;1234): 5 steps
lem-auto-CS01-∣-BOXd⟨0·1234⟩ : Complete 4 → ⟪ (CS01 ∷ Bx⁻0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-1234 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOXd⟨0·1234⟩ c4 = run b0
  where
  b0 : Chain (CS01 ∷ Bx⁻0-1234 ∷ []) (Bx⁻0-1234 ∷ CS01 ∷ [])
  b0 = at 1 1 (Bx0-1234 ∷ []) (lem-BOXd-BOX c4) ▸
       at 1 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 0 2 (Bx0-2134 ∷ CS01 ∷ []) (lem-CS20-beta-c-at1221 c4) ▸
       at 0 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸
       at 0 1 (Bx⁻0-1234 ∷ []) (sym (lem-BOXd-BOX c4)) ▸ done


-- auto CS01 | SBOXd(0;1;23;4): 11 steps
lem-auto-CS01-∣-SBOXd⟨0·1·23·4⟩ : Complete 4 → ⟪ (CS01 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-23-4 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOXd⟨0·1·23·4⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS01 ∷ Sb⁻0-1-23-4 ∷ []) (Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ CS01 ∷ Toff423 ∷ Bx⁻0-1234 ∷ [])
  b0 = at 1 1 (Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) (refl) ▸
       at 1 1 (CS14 ∷ []) (refl) ▸
       at 0 2 (CS14 ∷ CS01 ∷ []) (pw2 c4 (CS01 ∷ CS14 ∷ []) (CS14 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-1-4-3 ∷ []) (refl) ▸
       at 1 2 (Toff423 ∷ CS01 ∷ []) (lem-auto-CS01-∣-TOFF234-at243243 c4) ▸
       at 3 1 (CS14⁻ ∷ []) (refl) ▸
       at 2 2 (CS14⁻ ∷ CS01 ∷ []) (pw2 c4 (CS01 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸ done

  b1 : Chain (Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ CS01 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) (Sb⁻0-1-23-4 ∷ CS01 ∷ [])
  b1 = at 3 2 (Toff423 ∷ CS01 ∷ []) (lem-auto-CS01-∣-TOFF234-at243243 c4) ▸
       at 4 2 (Bx⁻0-1234 ∷ CS01 ∷ []) (lem-auto-CS01-∣-BOXd⟨0·1234⟩ c4) ▸
       at 0 5 (Sb⁻0-1-23-4 ∷ []) (refl) ▸ done


-- auto Kd0 | BOXd(0;1234): 3 steps
lem-auto-Kd0-∣-BOXd⟨0·1234⟩ : Complete 4 → ⟪ (K0⁻ ∷ Bx⁻0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-1234 ∷ K0⁻ ∷ []) ⟫ʷ
lem-auto-Kd0-∣-BOXd⟨0·1234⟩ c4 = run b0
  where
  b0 : Chain (K0⁻ ∷ Bx⁻0-1234 ∷ []) (Bx⁻0-1234 ∷ K0⁻ ∷ [])
  b0 = at 1 1 (Bx0-1234 ∷ []) (lem-BOXd-BOX c4) ▸
       at 0 2 (Bx0-1234 ∷ K0⁻ ∷ []) (lem-K0-pass-ci c4) ▸
       at 0 1 (Bx⁻0-1234 ∷ []) (sym (lem-BOXd-BOX c4)) ▸ done


-- F0d @0114203243: 5 steps
lem-F0d-at0114203243 : Complete 4 → ⟪ (Sb⁻0-1-34-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-1-34-0 ∷ []) ⟫ʷ
lem-F0d-at0114203243 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-34-2 ∷ []) (Sb⁻2-1-34-0 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻1-0-34-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·34·2⟩ c4) ▸
       at 1 1 (Sb⁻2-0-34-1 ∷ []) (lem-F0d-at14213243 c4) ▸
       at 0 2 (Sb⁻2-1-34-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨2·0·34·1⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- F0d @0214203143: 5 steps
lem-F0d-at0214203143 : Complete 4 → ⟪ (Sb⁻0-2-34-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-2-34-0 ∷ []) ⟫ʷ
lem-F0d-at0214203143 c4 = run b0
  where
  b0 : Chain (Sb⁻0-2-34-1 ∷ []) (Sb⁻1-2-34-0 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-34-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨0·2·34·1⟩ c4) ▸
       at 1 1 (Sb⁻2-1-34-0 ∷ []) (lem-F0d-at0114203243 c4) ▸
       at 0 2 (Sb⁻1-2-34-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·1·34·0⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- F0d @0214213043: 5 steps
lem-F0d-at0214213043 : Complete 4 → ⟪ (Sb⁻1-2-34-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-2-34-1 ∷ []) ⟫ʷ
lem-F0d-at0214213043 c4 = run b0
  where
  b0 : Chain (Sb⁻1-2-34-0 ∷ []) (Sb⁻0-2-34-1 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-2-34-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·2·34·0⟩ c4) ▸
       at 1 1 (Sb⁻1-2-34-0 ∷ []) (lem-F0d-at0214203143 c4) ▸
       at 0 2 (Sb⁻0-2-34-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·2·34·0⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto Kd0 | BOXd(0;1234) @3443: 7 steps
lem-auto-Kd0-∣-BOXd⟨0·1234⟩-at3443 : Complete 4 → ⟪ (K0⁻ ∷ Bx⁻0-1243 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-1243 ∷ K0⁻ ∷ []) ⟫ʷ
lem-auto-Kd0-∣-BOXd⟨0·1234⟩-at3443 c4 = run b0
  where
  b0 : Chain (K0⁻ ∷ Bx⁻0-1243 ∷ []) (Bx⁻0-1243 ∷ K0⁻ ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (K0⁻ ∷ Sw34 ∷ []) (sym (c₁ (K • iI) (Swap ↑ ↑))) ▸
       at 2 2 (Bx⁻0-1234 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·1243⟩ c4) ▸
       at 1 2 (Bx⁻0-1234 ∷ K0⁻ ∷ []) (lem-auto-Kd0-∣-BOXd⟨0·1234⟩ c4) ▸
       at 0 2 (Bx⁻0-1243 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·1234⟩ c4) ▸
       at 1 2 (K0⁻ ∷ Sw34 ∷ []) (sym (c₁ (K • iI) (Swap ↑ ↑))) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto Kd0 | BOXd(0;1234) @233442: 7 steps
lem-auto-Kd0-∣-BOXd⟨0·1234⟩-at233442 : Complete 4 → ⟪ (K0⁻ ∷ Bx⁻0-1342 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-1342 ∷ K0⁻ ∷ []) ⟫ʷ
lem-auto-Kd0-∣-BOXd⟨0·1234⟩-at233442 c4 = run b0
  where
  b0 : Chain (K0⁻ ∷ Bx⁻0-1342 ∷ []) (Bx⁻0-1342 ∷ K0⁻ ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (K0⁻ ∷ Sw23 ∷ []) (sym (c₁ (K • iI) (Swap ↑))) ▸
       at 2 2 (Bx⁻0-1243 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·1342⟩ c4) ▸
       at 1 2 (Bx⁻0-1243 ∷ K0⁻ ∷ []) (lem-auto-Kd0-∣-BOXd⟨0·1234⟩-at3443 c4) ▸
       at 0 2 (Bx⁻0-1342 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·1243⟩ c4) ▸
       at 1 2 (K0⁻ ∷ Sw23 ∷ []) (sym (c₁ (K • iI) (Swap ↑))) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto Kd0 | BOXd(0;1234) @12233441: 7 steps
lem-auto-Kd0-∣-BOXd⟨0·1234⟩-at12233441 : Complete 4 → ⟪ (K0⁻ ∷ Bx⁻0-2341 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-2341 ∷ K0⁻ ∷ []) ⟫ʷ
lem-auto-Kd0-∣-BOXd⟨0·1234⟩-at12233441 c4 = run b0
  where
  b0 : Chain (K0⁻ ∷ Bx⁻0-2341 ∷ []) (Bx⁻0-2341 ∷ K0⁻ ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (K0⁻ ∷ Sw12 ∷ []) (sym (c₁ (K • iI) (Swap))) ▸
       at 2 2 (Bx⁻0-1342 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·2341⟩ c4) ▸
       at 1 2 (Bx⁻0-1342 ∷ K0⁻ ∷ []) (lem-auto-Kd0-∣-BOXd⟨0·1234⟩-at233442 c4) ▸
       at 0 2 (Bx⁻0-2341 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·1342⟩ c4) ▸
       at 1 2 (K0⁻ ∷ Sw12 ∷ []) (sym (c₁ (K • iI) (Swap))) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto Kd0 | SBOXd(1;2;34;0): 13 steps
lem-auto-Kd0-∣-SBOXd⟨1·2·34·0⟩ : Complete 4 → ⟪ (K0⁻ ∷ Sb⁻1-2-34-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-2-34-0 ∷ K0⁻ ∷ []) ⟫ʷ
lem-auto-Kd0-∣-SBOXd⟨1·2·34·0⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (K0⁻ ∷ Sb⁻1-2-34-0 ∷ []) (Sb0-2-1-4 ∷ Toff134 ∷ CS12⁻ ∷ K0⁻ ∷ Toff134 ∷ Bx⁻0-2341 ∷ [])
  b0 = at 1 1 (Sb⁻0-2-34-1 ∷ []) (lem-F0d-at0214213043 c4) ▸
       at 1 1 (Sb0-2-1-4 ∷ Toff134 ∷ Sb⁻0-2-1-4 ∷ Toff134 ∷ Bx⁻0-2341 ∷ []) (refl) ▸
       at 1 1 (CS12 ∷ []) (refl) ▸
       at 0 2 (CS12 ∷ K0⁻ ∷ []) (lw4 c4 (K0⁻ ∷ CS12 ∷ []) (CS12 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-2-1-4 ∷ []) (refl) ▸
       at 1 2 (Toff134 ∷ K0⁻ ∷ []) (pw2 c4 (K0⁻ ∷ Toff134 ∷ []) (Toff134 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CS12⁻ ∷ []) (refl) ▸
       at 2 2 (CS12⁻ ∷ K0⁻ ∷ []) (lw4 c4 (K0⁻ ∷ CS12⁻ ∷ []) (CS12⁻ ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Sb0-2-1-4 ∷ Toff134 ∷ CS12⁻ ∷ K0⁻ ∷ Toff134 ∷ Bx⁻0-2341 ∷ []) (Sb⁻1-2-34-0 ∷ K0⁻ ∷ [])
  b1 = at 2 1 (Sb⁻0-2-1-4 ∷ []) (refl) ▸
       at 3 2 (Toff134 ∷ K0⁻ ∷ []) (pw2 c4 (K0⁻ ∷ Toff134 ∷ []) (Toff134 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx⁻0-2341 ∷ K0⁻ ∷ []) (lem-auto-Kd0-∣-BOXd⟨0·1234⟩-at12233441 c4) ▸
       at 0 5 (Sb⁻0-2-34-1 ∷ []) (refl) ▸
       at 0 1 (Sb⁻1-2-34-0 ∷ []) (sym (lem-F0d-at0214213043 c4)) ▸ done


-- BOXd-BOX @02233440: 5 steps
lem-BOXd-BOX-at02233440 : Complete 4 → ⟪ (Bx⁻2-1340 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1340 ∷ []) ⟫ʷ
lem-BOXd-BOX-at02233440 c4 = run b0
  where
  b0 : Chain (Bx⁻2-1340 ∷ []) (Bx2-1340 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx⁻2-0341 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨2·1340⟩ c4) ▸
       at 1 1 (Bx2-0341 ∷ []) (lem-BOXd-BOX-at0210233441 c4) ▸
       at 0 2 (Bx2-1340 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·0341⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CS01 | BOXd(2;1340): 9 steps
lem-auto-CS01-∣-BOXd⟨2·1340⟩ : Complete 4 → ⟪ (CS01 ∷ Bx⁻2-1340 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-1340 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOXd⟨2·1340⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS01 ∷ Bx⁻2-1340 ∷ []) (Bx2-1340 ∷ CS01 ∷ [])
  b0 = at 1 1 (Bx2-1340 ∷ []) (lem-BOXd-BOX-at02233440 c4) ▸
       at 0 1 (CS01 ∷ []) (lw4 c4 (CS01 ∷ []) (CS01 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx2-1304 ∷ []) (lem-sym34-at02233440 c4) ▸
       at 1 1 (Bx2-1034 ∷ []) (lem-sym23-at022330 c4) ▸
       at 0 2 (Bx2-1034 ∷ CS01 ∷ []) (lem-CS12-beta-at0220 c4) ▸
       at 0 1 (Bx2-1304 ∷ []) (lem-sym23-at0220 c4) ▸
       at 0 1 (Bx2-1340 ∷ []) (lem-sym34-at022330 c4) ▸
       at 1 1 (CS01 ∷ []) (lw4 c4 (CS01 ∷ []) (CS01 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Bx2-1340 ∷ CS01 ∷ []) (Bx⁻2-1340 ∷ CS01 ∷ [])
  b1 = at 0 1 (Bx⁻2-1340 ∷ []) (sym (lem-BOXd-BOX-at02233440 c4)) ▸ done


-- auto CS01 | SBOXd(2;1;34;0): 9 steps
lem-auto-CS01-∣-SBOXd⟨2·1·34·0⟩ : Complete 4 → ⟪ (CS01 ∷ Sb⁻2-1-34-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-1-34-0 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOXd⟨2·1·34·0⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS01 ∷ Sb⁻2-1-34-0 ∷ []) (Sb2-1-0-4 ∷ Toff034 ∷ Sb⁻2-1-0-4 ∷ Toff034 ∷ Bx⁻2-1340 ∷ CS01 ∷ [])
  b0 = at 1 1 (Sb2-1-0-4 ∷ Toff034 ∷ Sb⁻2-1-0-4 ∷ Toff034 ∷ Bx⁻2-1340 ∷ []) (refl) ▸
       at 1 1 (CS01 ∷ []) (refl) ▸
       at 0 2 (CS01 ∷ CS01 ∷ []) (lw4 c4 (CS01 ∷ CS01 ∷ []) (CS01 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb2-1-0-4 ∷ []) (refl) ▸
       at 3 1 (CS01⁻ ∷ []) (refl) ▸
       at 1 4 (Toff034 ∷ CS01⁻ ∷ Toff034 ∷ CS01 ∷ []) (pw2 c4 (CS01 ∷ Toff034 ∷ CS01⁻ ∷ Toff034 ∷ []) (Toff034 ∷ CS01⁻ ∷ Toff034 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb⁻2-1-0-4 ∷ []) (refl) ▸
       at 4 2 (Bx⁻2-1340 ∷ CS01 ∷ []) (lem-auto-CS01-∣-BOXd⟨2·1340⟩ c4) ▸ done

  b1 : Chain (Sb2-1-0-4 ∷ Toff034 ∷ Sb⁻2-1-0-4 ∷ Toff034 ∷ Bx⁻2-1340 ∷ CS01 ∷ []) (Sb⁻2-1-34-0 ∷ CS01 ∷ [])
  b1 = at 0 5 (Sb⁻2-1-34-0 ∷ []) (refl) ▸ done


-- auto SBOXd(0;1;23;4) | CCZ143: 26 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ143 : Complete 4 → ⟪ (Sb⁻0-1-23-4 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ143 c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Sb⁻0-1-23-4 ∷ CCZ134 ∷ []) (CS13 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ Toff423 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CX43 ∷ CS13⁻ ∷ CCZ024 ∷ CX43 ∷ CS14 ∷ [])
  b0 = at 1 1 (CS13 ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ CS14 ∷ []) (lw0 c4 (CCZ134 ∷ []) (CS13 ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻0-1-32-4 ∷ []) (lem-SBsymd-at0113203442 c4) ▸
       at 0 2 (CS13 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS21-at2332 c4) ▸
       at 1 1 (Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ Toff423 ∷ Bx⁻0-1324 ∷ []) (refl) ▸
       at 5 1 (Bx0-1324 ∷ []) (lem-BOXd-BOX-at2332 c4) ▸
       at 5 1 (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-beta-T-at2332 c4) ▸
       at 8 2 (CX43 ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ CX43 ∷ []) (CX43 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CS13⁻ ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CSd13 c4) ▸ done

  b1 : Chain (CS13 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ Toff423 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CX43 ∷ CS13⁻ ∷ CCZ024 ∷ CX43 ∷ CS14 ∷ []) (CS13 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ Toff423 ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ Bx⁻0-1324 ∷ CS14 ∷ [])
  b1 = at 10 2 (CX43 ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ CX43 ∷ []) (CX43 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 7 4 (CX43 ∷ CS13⁻ ∷ CX43 ∷ Toff013 ∷ []) (pw2 c4 (Toff013 ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ []) (CX43 ∷ CS13⁻ ∷ CX43 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CX43 ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ CX43 ∷ []) (CX43 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CS13⁻ ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CSd13 c4) ▸
       at 8 2 (CX43 ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ CX43 ∷ []) (CX43 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 5 4 (CX43 ∷ CS13⁻ ∷ CX43 ∷ Toff013 ∷ []) (pw2 c4 (Toff013 ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ []) (CX43 ∷ CS13⁻ ∷ CX43 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 8 4 (Bx0-1324 ∷ []) (sym (lem-beta-T-at2332 c4)) ▸
       at 8 1 (Bx⁻0-1324 ∷ []) (sym (lem-BOXd-BOX-at2332 c4)) ▸ done

  b2 : Chain (CS13 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ Toff423 ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ Bx⁻0-1324 ∷ CS14 ∷ []) (CS13 ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ CS14 ∷ Sb⁻0-1-32-4 ∷ [])
  b2 = at 3 1 (CS14⁻ ∷ []) (refl) ▸
       at 2 6 (CX43 ∷ CS13⁻ ∷ CX43 ∷ Toff423 ∷ CS14⁻ ∷ Toff423 ∷ []) (lw0 c4 (Toff423 ∷ CS14⁻ ∷ Toff423 ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ []) (CX43 ∷ CS13⁻ ∷ CX43 ∷ Toff423 ∷ CS14⁻ ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sb⁻0-1-4-2 ∷ []) (refl) ▸
       at 1 1 (CS14 ∷ []) (refl) ▸
       at 1 4 (CX43 ∷ CS13⁻ ∷ CX43 ∷ CS14 ∷ []) (lw0 c4 (CS14 ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ []) (CX43 ∷ CS13⁻ ∷ CX43 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb0-1-4-2 ∷ []) (refl) ▸
       at 4 5 (Sb⁻0-1-32-4 ∷ []) (refl) ▸
       at 4 2 (CS14 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS41-at2332 c4) ▸ done

  b3 : Chain (CS13 ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ CS14 ∷ Sb⁻0-1-32-4 ∷ []) (CCZ134 ∷ Sb⁻0-1-23-4 ∷ [])
  b3 = at 5 1 (Sb⁻0-1-23-4 ∷ []) (sym (lem-SBsymd-at0113203442 c4)) ▸
       at 0 5 (CCZ134 ∷ []) (lw0 c4 (CS13 ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ CS14 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | CS02 @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS02-at2332 : Complete 4 → ⟪ (Sb⁻0-1-32-4 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS02-at2332 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-32-4 ∷ CS03 ∷ []) (CS03 ∷ Sb⁻0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·32·4⟩ c4) ▸
       at 2 2 (CS02 ∷ Sw23 ∷ []) (lem-nat-2-CS03 c4) ▸
       at 1 2 (CS02 ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS02 c4) ▸
       at 0 2 (CS03 ∷ Sw23 ∷ []) (lem-nat-2-CS02 c4) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | SBOX(1;0;3;4): 5 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩ : Complete 4 → ⟪ (Sb⁻0-1-23-4 ∷ Sb1-0-3-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-3-4 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩ c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-23-4 ∷ Sb1-0-3-4 ∷ []) (Sb1-0-3-4 ∷ Sb⁻0-1-23-4 ∷ [])
  b0 = at 1 1 (CS03 ∷ []) (refl) ▸
       at 0 1 (Sb⁻0-1-32-4 ∷ []) (lem-SBsymd-at0113203442 c4) ▸
       at 0 2 (CS03 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS02-at2332 c4) ▸
       at 1 1 (Sb⁻0-1-23-4 ∷ []) (sym (lem-SBsymd-at0113203442 c4)) ▸
       at 0 1 (Sb1-0-3-4 ∷ []) (refl) ▸ done


-- auto BOXd(0;1234) | CSd02: 3 steps
lem-auto-BOXd⟨0·1234⟩-∣-CSd02 : Complete 4 → ⟪ (Bx⁻0-1234 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ Bx⁻0-1234 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CSd02 c4 = run b0
  where
  b0 : Chain (Bx⁻0-1234 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ Bx⁻0-1234 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ []) (lem-BOXd-BOX c4) ▸
       at 0 2 (CS02⁻ ∷ Bx0-1234 ∷ []) (sym (lem-CS20-beta-ci c4)) ▸
       at 1 1 (Bx⁻0-1234 ∷ []) (sym (lem-BOXd-BOX c4)) ▸ done


-- auto SBOXd(0;1;23;4) | CSd02: 11 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CSd02 : Complete 4 → ⟪ (Sb⁻0-1-23-4 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CSd02 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb⁻0-1-23-4 ∷ CS02⁻ ∷ []) (CS14 ∷ CS02⁻ ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ [])
  b0 = at 0 1 (Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) (refl) ▸
       at 4 2 (CS02⁻ ∷ Bx⁻0-1234 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-CSd02 c4) ▸
       at 3 2 (CS02⁻ ∷ Toff423 ∷ []) (pw1 c4 (Toff423 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CS14⁻ ∷ []) (refl) ▸
       at 2 2 (CS02⁻ ∷ CS14⁻ ∷ []) (pw3 c4 (CS14⁻ ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 1 2 (CS02⁻ ∷ Toff423 ∷ []) (pw1 c4 (Toff423 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (CS14 ∷ []) (refl) ▸ done

  b1 : Chain (CS14 ∷ CS02⁻ ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) (CS02⁻ ∷ Sb⁻0-1-23-4 ∷ [])
  b1 = at 0 2 (CS02⁻ ∷ CS14 ∷ []) (pw3 c4 (CS14 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Sb0-1-4-3 ∷ []) (refl) ▸
       at 1 5 (Sb⁻0-1-23-4 ∷ []) (refl) ▸ done


-- auto SBOXd(0;1;23;4) | CSd02 @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CSd02-at2332 : Complete 4 → ⟪ (Sb⁻0-1-32-4 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CSd02-at2332 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-32-4 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Sb⁻0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·32·4⟩ c4) ▸
       at 2 2 (CS02⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd03 c4) ▸
       at 1 2 (CS02⁻ ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CSd02 c4) ▸
       at 0 2 (CS03⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd02 c4) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | SBOXd(1;0;3;4): 5 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩ : Complete 4 → ⟪ (Sb⁻0-1-23-4 ∷ Sb⁻1-0-3-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-3-4 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩ c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-23-4 ∷ Sb⁻1-0-3-4 ∷ []) (Sb⁻1-0-3-4 ∷ Sb⁻0-1-23-4 ∷ [])
  b0 = at 1 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 1 (Sb⁻0-1-32-4 ∷ []) (lem-SBsymd-at0113203442 c4) ▸
       at 0 2 (CS03⁻ ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CSd02-at2332 c4) ▸
       at 1 1 (Sb⁻0-1-23-4 ∷ []) (sym (lem-SBsymd-at0113203442 c4)) ▸
       at 0 1 (Sb⁻1-0-3-4 ∷ []) (refl) ▸ done


-- AX-SB @3443: 7 steps
lem-AX-SB-at3443 : Complete 4 → ⟪ (CS01 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ CS01 ∷ []) ⟫ʷ
lem-AX-SB-at3443 c4 = run b0
  where
  b0 : Chain (CS01 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ CS01 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 2 2 (Sb0-2-34-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·2·43·1⟩ c4) ▸
       at 1 2 (Sb0-2-34-1 ∷ CS01 ∷ []) (lem-AX-SB c4) ▸
       at 0 2 (Sb0-2-43-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·2·34·1⟩ c4) ▸
       at 1 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | CCZ143 @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ143-at2332 : Complete 4 → ⟪ (Sb⁻0-1-32-4 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ143-at2332 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-32-4 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sb⁻0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·32·4⟩ c4) ▸
       at 2 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 1 2 (CCZ134 ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ143 c4) ▸
       at 0 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | CCZ143 @243243: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ143-at243243 : Complete 4 → ⟪ (Sb⁻0-1-42-3 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Sb⁻0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ143-at243243 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-42-3 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sb⁻0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·42·3⟩ c4) ▸
       at 2 2 (CCZ124 ∷ Sw34 ∷ []) (lem-nat-3-CCZ123 c4) ▸
       at 1 2 (CCZ124 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ143-at2332 c4) ▸
       at 0 2 (CCZ123 ∷ Sw34 ∷ []) (lem-nat-3-CCZ124 c4) ▸
       at 1 2 (Sb⁻0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·32·4⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | CCZ143 @0110243243: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ143-at0110243243 : Complete 4 → ⟪ (Sb⁻1-0-42-3 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Sb⁻1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ143-at0110243243 c4 = run b0
  where
  b0 : Chain (Sb⁻1-0-42-3 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sb⁻1-0-42-3 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·42·3⟩ c4) ▸
       at 2 2 (CCZ123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ023 ∷ []) (CCZ123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ123 ∷ Sb⁻0-1-42-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ143-at243243 c4) ▸
       at 0 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | CCZ143 @0210243143: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ143-at0210243143 : Complete 4 → ⟪ (Sb⁻2-0-41-3 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Sb⁻2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ143-at0210243143 c4 = run b0
  where
  b0 : Chain (Sb⁻2-0-41-3 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sb⁻2-0-41-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·41·3⟩ c4) ▸
       at 2 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 1 2 (CCZ023 ∷ Sb⁻1-0-42-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ143-at0110243243 c4) ▸
       at 0 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 1 2 (Sb⁻2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·0·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | SBOX(1;0;3;4) @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at2332 : Complete 4 → ⟪ (Sb⁻0-1-32-4 ∷ Sb1-0-2-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-2-4 ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-32-4 ∷ Sb1-0-2-4 ∷ []) (Sb1-0-2-4 ∷ Sb⁻0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·32·4⟩ c4) ▸
       at 2 2 (Sb1-0-3-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·2·4⟩ c4) ▸
       at 1 2 (Sb1-0-3-4 ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩ c4) ▸
       at 0 2 (Sb1-0-2-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·3·4⟩ c4) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | SBOX(1;0;3;4) @243243: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at243243 : Complete 4 → ⟪ (Sb⁻0-1-42-3 ∷ Sb1-0-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-2-3 ∷ Sb⁻0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-42-3 ∷ Sb1-0-2-3 ∷ []) (Sb1-0-2-3 ∷ Sb⁻0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·42·3⟩ c4) ▸
       at 2 2 (Sb1-0-2-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·0·2·3⟩ c4) ▸
       at 1 2 (Sb1-0-2-4 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at2332 c4) ▸
       at 0 2 (Sb1-0-2-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·0·2·4⟩ c4) ▸
       at 1 2 (Sb⁻0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·32·4⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | SBOX(1;0;3;4) @0110243243: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at0110243243 : Complete 4 → ⟪ (Sb⁻1-0-42-3 ∷ Sb0-1-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-2-3 ∷ Sb⁻1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at0110243243 c4 = run b0
  where
  b0 : Chain (Sb⁻1-0-42-3 ∷ Sb0-1-2-3 ∷ []) (Sb0-1-2-3 ∷ Sb⁻1-0-42-3 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·42·3⟩ c4) ▸
       at 2 2 (Sb1-0-2-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·2·3⟩ c4) ▸
       at 1 2 (Sb1-0-2-3 ∷ Sb⁻0-1-42-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at243243 c4) ▸
       at 0 2 (Sb0-1-2-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·2·3⟩ c4) ▸
       at 1 2 (Sb⁻1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | SBOX(1;0;3;4) @0210243143: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at0210243143 : Complete 4 → ⟪ (Sb⁻2-0-41-3 ∷ Sb0-2-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-1-3 ∷ Sb⁻2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at0210243143 c4 = run b0
  where
  b0 : Chain (Sb⁻2-0-41-3 ∷ Sb0-2-1-3 ∷ []) (Sb0-2-1-3 ∷ Sb⁻2-0-41-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·41·3⟩ c4) ▸
       at 2 2 (Sb0-1-2-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·1·3⟩ c4) ▸
       at 1 2 (Sb0-1-2-3 ∷ Sb⁻1-0-42-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at0110243243 c4) ▸
       at 0 2 (Sb0-2-1-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·2·3⟩ c4) ▸
       at 1 2 (Sb⁻2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·0·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | SBOXd(1;0;3;4) @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at2332 : Complete 4 → ⟪ (Sb⁻0-1-32-4 ∷ Sb⁻1-0-2-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-2-4 ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-32-4 ∷ Sb⁻1-0-2-4 ∷ []) (Sb⁻1-0-2-4 ∷ Sb⁻0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·32·4⟩ c4) ▸
       at 2 2 (Sb⁻1-0-3-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·2·4⟩ c4) ▸
       at 1 2 (Sb⁻1-0-3-4 ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩ c4) ▸
       at 0 2 (Sb⁻1-0-2-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·3·4⟩ c4) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | SBOXd(1;0;3;4) @243243: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at243243 : Complete 4 → ⟪ (Sb⁻0-1-42-3 ∷ Sb⁻1-0-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-2-3 ∷ Sb⁻0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-42-3 ∷ Sb⁻1-0-2-3 ∷ []) (Sb⁻1-0-2-3 ∷ Sb⁻0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·42·3⟩ c4) ▸
       at 2 2 (Sb⁻1-0-2-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨1·0·2·3⟩ c4) ▸
       at 1 2 (Sb⁻1-0-2-4 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at2332 c4) ▸
       at 0 2 (Sb⁻1-0-2-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨1·0·2·4⟩ c4) ▸
       at 1 2 (Sb⁻0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·32·4⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | SBOXd(1;0;3;4) @0110243243: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at0110243243 : Complete 4 → ⟪ (Sb⁻1-0-42-3 ∷ Sb⁻0-1-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-2-3 ∷ Sb⁻1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at0110243243 c4 = run b0
  where
  b0 : Chain (Sb⁻1-0-42-3 ∷ Sb⁻0-1-2-3 ∷ []) (Sb⁻0-1-2-3 ∷ Sb⁻1-0-42-3 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·42·3⟩ c4) ▸
       at 2 2 (Sb⁻1-0-2-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·2·3⟩ c4) ▸
       at 1 2 (Sb⁻1-0-2-3 ∷ Sb⁻0-1-42-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at243243 c4) ▸
       at 0 2 (Sb⁻0-1-2-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·2·3⟩ c4) ▸
       at 1 2 (Sb⁻1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | SBOXd(1;0;3;4) @0210243143: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at0210243143 : Complete 4 → ⟪ (Sb⁻2-0-41-3 ∷ Sb⁻0-2-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-2-1-3 ∷ Sb⁻2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at0210243143 c4 = run b0
  where
  b0 : Chain (Sb⁻2-0-41-3 ∷ Sb⁻0-2-1-3 ∷ []) (Sb⁻0-2-1-3 ∷ Sb⁻2-0-41-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·41·3⟩ c4) ▸
       at 2 2 (Sb⁻0-1-2-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨0·2·1·3⟩ c4) ▸
       at 1 2 (Sb⁻0-1-2-3 ∷ Sb⁻1-0-42-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at0110243243 c4) ▸
       at 0 2 (Sb⁻0-2-1-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨0·1·2·3⟩ c4) ▸
       at 1 2 (Sb⁻2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·0·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


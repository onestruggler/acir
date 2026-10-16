{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D011 where

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
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-T-beta ; lem-auto-TOFF012-∣-CCZ324 ; lem-beta-T)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-sym23-at1221)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-CX10-beta-c-at0110 ; lem-CZ10-beta-c-at011220 ; lem-CZ10-beta-c-at1221 ; lem-sym12-at0110 ; lem-sym12-at011220 ; lem-sym23-at011220 ; lem-sym23-at01122330 ; lem-sym23-at122331 ; lem-sym23-at243243 ; lem-sym23-at3443 ; lem-sym34-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-CS20-beta-c-at1221 ; lem-SBsym ; lem-sym34-at122331 ; lem-sym34-at12233441)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-F5-CS01 ; lem-auto-Kd0-∣-BOX⟨0·1234⟩ ; lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩ ; lem-auto-SBOXd⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.D007 using (lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩ ; lem-auto-K0-∣-BOX⟨0·1234⟩ ; lem-auto-K0-∣-SBOX⟨1·2·34·0⟩)
open import Examples.Groups.Clifford+CS.Five.D.D010 using (lem-CS20-beta-ci-at011220 ; lem-CS20-beta-ci-at1221 ; lem-sym34-at01122330 ; lem-sym34-at0112233440)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-2-CCZ034 ; lem-nat-2-TOFF012 ; lem-nat-3-BOX⟨0·1243⟩ ; lem-nat-3-BOX⟨0·1423⟩ ; lem-nat-3-CCZ034)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-CCZ024 ; lem-nat-1-TOFF103)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-0-CCZ034)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-0-BOX⟨0·1423⟩ ; lem-nat-1-BOX⟨1·0423⟩)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-0-BOX⟨1·0243⟩ ; lem-nat-0-BOX⟨1·0423⟩ ; lem-nat-1-BOX⟨2·0143⟩ ; lem-nat-1-BOX⟨2·0413⟩)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-nat-0-BOX⟨0·2134⟩ ; lem-nat-0-BOX⟨1·2034⟩ ; lem-nat-2-BOX⟨0·1243⟩ ; lem-nat-2-BOX⟨0·1342⟩)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-nat-1-CS01 ; lem-nat-1-CS02)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-0-CS04 ; lem-nat-0-CS14 ; lem-nat-0-SBOX⟨0·1·42·3⟩ ; lem-nat-0-SBOX⟨1·0·42·3⟩ ; lem-nat-0-SBOXd⟨0·1·3·2⟩ ; lem-nat-0-SBOXd⟨1·0·3·2⟩ ; lem-nat-1-CS04 ; lem-nat-1-SBOX⟨1·0·42·3⟩ ; lem-nat-1-SBOX⟨2·0·41·3⟩ ; lem-nat-1-SBOXd⟨1·0·3·2⟩ ; lem-nat-1-SBOXd⟨2·0·3·1⟩ ; lem-nat-2-BOX⟨0·1432⟩ ; lem-nat-2-CS02 ; lem-nat-2-SBOX⟨1·0·43·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-0-BOX⟨0·1342⟩ ; lem-nat-3-SBOX⟨1·0·34·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R016 using (lem-nat-0-BOX⟨1·0342⟩ ; lem-nat-1-BOX⟨1·0342⟩ ; lem-nat-1-BOX⟨2·0341⟩ ; lem-nat-3-CS04)
open import Examples.Groups.Clifford+CS.Five.D.R017 using (lem-nat-2-CS04 ; lem-nat-3-CS03)
open import Examples.Groups.Clifford+CS.Five.D.R019 using (lem-nat-2-BOX⟨0·1423⟩ ; lem-nat-2-CS03 ; lem-nat-2-SBOXd⟨0·1·2·3⟩ ; lem-nat-2-SBOXd⟨0·1·3·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R020 using (lem-nat-1-SBOX⟨2·0·14·3⟩ ; lem-nat-2-SBOX⟨0·1·42·3⟩ ; lem-nat-2-SBOX⟨0·1·43·2⟩ ; lem-nat-2-SBOX⟨1·0·24·3⟩ ; lem-nat-3-SBOX⟨1·2·34·0⟩ ; lem-nat-3-SBOX⟨1·2·43·0⟩)
open import Examples.Groups.Clifford+CS.Five.D.R021 using (lem-nat-0-BOX⟨0·1432⟩ ; lem-nat-0-SBOX⟨0·2·43·1⟩ ; lem-nat-0-SBOX⟨1·2·43·0⟩ ; lem-nat-0-SBOX⟨2·3·04·1⟩ ; lem-nat-0-SBOX⟨2·3·14·0⟩ ; lem-nat-1-BOX⟨1·0432⟩ ; lem-nat-1-SBOX⟨0·1·43·2⟩ ; lem-nat-1-SBOX⟨0·2·43·1⟩ ; lem-nat-1-SBOX⟨1·3·24·0⟩ ; lem-nat-1-SBOX⟨2·3·14·0⟩ ; lem-nat-2-SBOX⟨1·2·34·0⟩ ; lem-nat-2-SBOX⟨1·3·24·0⟩ ; lem-nat-3-BOX⟨0·1342⟩)
open import Examples.Groups.Clifford+CS.Five.D.R022 using (lem-nat-0-BOX⟨1·0432⟩ ; lem-nat-1-BOX⟨2·0431⟩)
-- auto CSd01 | BOX(1;2340): 7 steps
lem-auto-CSd01-∣-BOX⟨1·2340⟩ : Complete 4 → ⟪ (CS01⁻ ∷ Bx1-2340 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2340 ∷ CS01⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨1·2340⟩ c4 = run b0
  where
  b0 : Chain (CS01⁻ ∷ Bx1-2340 ∷ []) (Bx1-2340 ∷ CS01⁻ ∷ [])
  b0 = at 0 1 (CS01⁻ ∷ []) (lw4 c4 (CS01⁻ ∷ []) (CS01⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx1-2304 ∷ []) (lem-sym34-at0112233440 c4) ▸
       at 1 1 (Bx1-2034 ∷ []) (lem-sym23-at01122330 c4) ▸
       at 0 2 (Bx1-2034 ∷ CS01⁻ ∷ []) (lem-CS20-beta-ci-at011220 c4) ▸
       at 0 1 (Bx1-2304 ∷ []) (lem-sym23-at011220 c4) ▸
       at 0 1 (Bx1-2340 ∷ []) (lem-sym34-at01122330 c4) ▸
       at 1 1 (CS01⁻ ∷ []) (lw4 c4 (CS01⁻ ∷ []) (CS01⁻ ∷ []) tt tt Eq.refl) ▸ done


-- auto CSd01 | BOX(0;2341): 5 steps
lem-auto-CSd01-∣-BOX⟨0·2341⟩ : Complete 4 → ⟪ (CS01⁻ ∷ Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ CS01⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨0·2341⟩ c4 = run b0
  where
  b0 : Chain (CS01⁻ ∷ Bx0-2341 ∷ []) (Bx0-2341 ∷ CS01⁻ ∷ [])
  b0 = at 1 1 (Bx0-2314 ∷ []) (lem-sym34-at12233441 c4) ▸
       at 1 1 (Bx0-2134 ∷ []) (lem-sym23-at122331 c4) ▸
       at 0 2 (Bx0-2134 ∷ CS01⁻ ∷ []) (lem-CS20-beta-ci-at1221 c4) ▸
       at 0 1 (Bx0-2314 ∷ []) (lem-sym23-at1221 c4) ▸
       at 0 1 (Bx0-2341 ∷ []) (lem-sym34-at122331 c4) ▸ done


-- CS20-beta-c @011220: 7 steps
lem-CS20-beta-c-at011220 : Complete 4 → ⟪ (CS01 ∷ Bx1-2034 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2034 ∷ CS01 ∷ []) ⟫ʷ
lem-CS20-beta-c-at011220 c4 = run b0
  where
  b0 : Chain (CS01 ∷ Bx1-2034 ∷ []) (Bx1-2034 ∷ CS01 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS01 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS01 ∷ []) (CS01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-2134 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2034⟩ c4) ▸
       at 1 2 (Bx0-2134 ∷ CS01 ∷ []) (lem-CS20-beta-c-at1221 c4) ▸
       at 0 2 (Bx1-2034 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2134⟩ c4) ▸
       at 1 2 (CS01 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS01 ∷ []) (CS01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CS01 | BOX(1;2340): 7 steps
lem-auto-CS01-∣-BOX⟨1·2340⟩ : Complete 4 → ⟪ (CS01 ∷ Bx1-2340 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2340 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨1·2340⟩ c4 = run b0
  where
  b0 : Chain (CS01 ∷ Bx1-2340 ∷ []) (Bx1-2340 ∷ CS01 ∷ [])
  b0 = at 0 1 (CS01 ∷ []) (lw4 c4 (CS01 ∷ []) (CS01 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx1-2304 ∷ []) (lem-sym34-at0112233440 c4) ▸
       at 1 1 (Bx1-2034 ∷ []) (lem-sym23-at01122330 c4) ▸
       at 0 2 (Bx1-2034 ∷ CS01 ∷ []) (lem-CS20-beta-c-at011220 c4) ▸
       at 0 1 (Bx1-2304 ∷ []) (lem-sym23-at011220 c4) ▸
       at 0 1 (Bx1-2340 ∷ []) (lem-sym34-at01122330 c4) ▸
       at 1 1 (CS01 ∷ []) (lw4 c4 (CS01 ∷ []) (CS01 ∷ []) tt tt Eq.refl) ▸ done


-- auto CX01 | BOX(1;2340): 7 steps
lem-auto-CX01-∣-BOX⟨1·2340⟩ : Complete 4 → ⟪ (CX01 ∷ Bx1-2340 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2340 ∷ CX01 ∷ []) ⟫ʷ
lem-auto-CX01-∣-BOX⟨1·2340⟩ c4 = run b0
  where
  b0 : Chain (CX01 ∷ Bx1-2340 ∷ []) (Bx1-2340 ∷ CX01 ∷ [])
  b0 = at 1 1 (Bx1-2304 ∷ []) (lem-sym34-at0112233440 c4) ▸
       at 1 1 (Bx1-2034 ∷ []) (lem-sym23-at01122330 c4) ▸
       at 1 1 (Bx1-0234 ∷ []) (lem-sym12-at011220 c4) ▸
       at 0 2 (Bx1-0234 ∷ CX01 ∷ []) (lem-CX10-beta-c-at0110 c4) ▸
       at 0 1 (Bx1-2034 ∷ []) (lem-sym12-at0110 c4) ▸
       at 0 1 (Bx1-2304 ∷ []) (lem-sym23-at011220 c4) ▸
       at 0 1 (Bx1-2340 ∷ []) (lem-sym34-at01122330 c4) ▸ done


-- auto CZ01 | BOX(0;2341): 5 steps
lem-auto-CZ01-∣-BOX⟨0·2341⟩ : Complete 4 → ⟪ (CZ01 ∷ Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ CZ01 ∷ []) ⟫ʷ
lem-auto-CZ01-∣-BOX⟨0·2341⟩ c4 = run b0
  where
  b0 : Chain (CZ01 ∷ Bx0-2341 ∷ []) (Bx0-2341 ∷ CZ01 ∷ [])
  b0 = at 1 1 (Bx0-2314 ∷ []) (lem-sym34-at12233441 c4) ▸
       at 1 1 (Bx0-2134 ∷ []) (lem-sym23-at122331 c4) ▸
       at 0 2 (Bx0-2134 ∷ CZ01 ∷ []) (lem-CZ10-beta-c-at1221 c4) ▸
       at 0 1 (Bx0-2314 ∷ []) (lem-sym23-at1221 c4) ▸
       at 0 1 (Bx0-2341 ∷ []) (lem-sym34-at122331 c4) ▸ done


-- auto CZ01 | BOX(1;2340): 7 steps
lem-auto-CZ01-∣-BOX⟨1·2340⟩ : Complete 4 → ⟪ (CZ01 ∷ Bx1-2340 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2340 ∷ CZ01 ∷ []) ⟫ʷ
lem-auto-CZ01-∣-BOX⟨1·2340⟩ c4 = run b0
  where
  b0 : Chain (CZ01 ∷ Bx1-2340 ∷ []) (Bx1-2340 ∷ CZ01 ∷ [])
  b0 = at 0 1 (CZ01 ∷ []) (lw4 c4 (CZ01 ∷ []) (CZ01 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx1-2304 ∷ []) (lem-sym34-at0112233440 c4) ▸
       at 1 1 (Bx1-2034 ∷ []) (lem-sym23-at01122330 c4) ▸
       at 0 2 (Bx1-2034 ∷ CZ01 ∷ []) (lem-CZ10-beta-c-at011220 c4) ▸
       at 0 1 (Bx1-2304 ∷ []) (lem-sym23-at011220 c4) ▸
       at 0 1 (Bx1-2340 ∷ []) (lem-sym34-at01122330 c4) ▸
       at 1 1 (CZ01 ∷ []) (lw4 c4 (CZ01 ∷ []) (CZ01 ∷ []) tt tt Eq.refl) ▸ done


-- auto Kd0 | SBOX(0;1;23;4): 11 steps
lem-auto-Kd0-∣-SBOX⟨0·1·23·4⟩ : Complete 4 → ⟪ (K0⁻ ∷ Sb0-1-23-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-23-4 ∷ K0⁻ ∷ []) ⟫ʷ
lem-auto-Kd0-∣-SBOX⟨0·1·23·4⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (K0⁻ ∷ Sb0-1-23-4 ∷ []) (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ K0⁻ ∷ CS14⁻ ∷ [])
  b0 = at 1 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 0 2 (Bx0-1234 ∷ K0⁻ ∷ []) (lem-auto-Kd0-∣-BOX⟨0·1234⟩ c4) ▸
       at 1 2 (Toff423 ∷ K0⁻ ∷ []) (lw1 c4 (K0⁻ ∷ Toff423 ∷ []) (Toff423 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CS14 ∷ []) (refl) ▸
       at 2 2 (CS14 ∷ K0⁻ ∷ []) (pw2 c4 (K0⁻ ∷ CS14 ∷ []) (CS14 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb0-1-4-3 ∷ []) (refl) ▸
       at 3 2 (Toff423 ∷ K0⁻ ∷ []) (lw1 c4 (K0⁻ ∷ Toff423 ∷ []) (Toff423 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS14⁻ ∷ []) (refl) ▸ done

  b1 : Chain (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ K0⁻ ∷ CS14⁻ ∷ []) (Sb0-1-23-4 ∷ K0⁻ ∷ [])
  b1 = at 4 2 (CS14⁻ ∷ K0⁻ ∷ []) (pw2 c4 (K0⁻ ∷ CS14⁻ ∷ []) (CS14⁻ ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- auto K0 | SBOX(0;1;23;4): 11 steps
lem-auto-K0-∣-SBOX⟨0·1·23·4⟩ : Complete 4 → ⟪ (K0 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-23-4 ∷ K0 ∷ []) ⟫ʷ
lem-auto-K0-∣-SBOX⟨0·1·23·4⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (K0 ∷ Sb0-1-23-4 ∷ []) (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ K0 ∷ CS14⁻ ∷ [])
  b0 = at 1 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 0 2 (Bx0-1234 ∷ K0 ∷ []) (lem-auto-K0-∣-BOX⟨0·1234⟩ c4) ▸
       at 1 2 (Toff423 ∷ K0 ∷ []) (lw1 c4 (K0 ∷ Toff423 ∷ []) (Toff423 ∷ K0 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CS14 ∷ []) (refl) ▸
       at 2 2 (CS14 ∷ K0 ∷ []) (pw2 c4 (K0 ∷ CS14 ∷ []) (CS14 ∷ K0 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb0-1-4-3 ∷ []) (refl) ▸
       at 3 2 (Toff423 ∷ K0 ∷ []) (lw1 c4 (K0 ∷ Toff423 ∷ []) (Toff423 ∷ K0 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS14⁻ ∷ []) (refl) ▸ done

  b1 : Chain (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ K0 ∷ CS14⁻ ∷ []) (Sb0-1-23-4 ∷ K0 ∷ [])
  b1 = at 4 2 (CS14⁻ ∷ K0 ∷ []) (pw2 c4 (K0 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ K0 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- auto TOFF012 | BOX(0;1234): 1 steps
lem-auto-TOFF012-∣-BOX⟨0·1234⟩ : Complete 4 → ⟪ (Toff012 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ Toff012 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-BOX⟨0·1234⟩ c4 = run b0
  where
  b0 : Chain (Toff012 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ Toff012 ∷ [])
  b0 = at 0 2 (Bx0-1234 ∷ Toff012 ∷ []) (lem-T-beta c4) ▸ done


-- auto TOFF012 | TOFF324: 5 steps
lem-auto-TOFF012-∣-TOFF324 : Complete 4 → ⟪ (Toff012 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ Toff012 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-TOFF324 c4 = run b0
  where
  b0 : Chain (Toff012 ∷ Toff324 ∷ []) (Toff324 ∷ Toff012 ∷ [])
  b0 = at 1 1 (K3 ∷ CCZ234 ∷ K3⁻ ∷ []) (lw0 c4 (Toff324 ∷ []) (K3 ∷ CCZ234 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 0 2 (K3 ∷ Toff012 ∷ []) (lw4 c4 (Toff012 ∷ K3 ∷ []) (K3 ∷ Toff012 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ234 ∷ Toff012 ∷ []) (lem-auto-TOFF012-∣-CCZ324 c4) ▸
       at 2 2 (K3⁻ ∷ Toff012 ∷ []) (lw4 c4 (Toff012 ∷ K3⁻ ∷ []) (K3⁻ ∷ Toff012 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Toff324 ∷ []) (lw0 c4 (K3 ∷ CCZ234 ∷ K3⁻ ∷ []) (Toff324 ∷ []) tt tt Eq.refl) ▸ done


-- auto TOFF012 | TOFF324 @3443: 7 steps
lem-auto-TOFF012-∣-TOFF324-at3443 : Complete 4 → ⟪ (Toff012 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ Toff012 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-TOFF324-at3443 c4 = run b0
  where
  b0 : Chain (Toff012 ∷ Toff423 ∷ []) (Toff423 ∷ Toff012 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff012 ∷ Sw34 ∷ []) (sym (c₃ (Toff) (Swap))) ▸
       at 2 2 (Toff324 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff423 ∷ []) (Toff324 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff324 ∷ Toff012 ∷ []) (lem-auto-TOFF012-∣-TOFF324 c4) ▸
       at 0 2 (Toff423 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff324 ∷ []) (Toff423 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff012 ∷ Sw34 ∷ []) (sym (c₃ (Toff) (Swap))) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto TOFF012 | SBOX(0;1;23;4): 11 steps
lem-auto-TOFF012-∣-SBOX⟨0·1·23·4⟩ : Complete 4 → ⟪ (Toff012 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-23-4 ∷ Toff012 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-SBOX⟨0·1·23·4⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff012 ∷ Sb0-1-23-4 ∷ []) (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Toff012 ∷ CS14⁻ ∷ [])
  b0 = at 1 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 0 2 (Bx0-1234 ∷ Toff012 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·1234⟩ c4) ▸
       at 1 2 (Toff423 ∷ Toff012 ∷ []) (lem-auto-TOFF012-∣-TOFF324-at3443 c4) ▸
       at 3 1 (CS14 ∷ []) (refl) ▸
       at 2 2 (CS14 ∷ Toff012 ∷ []) (pw3 c4 (Toff012 ∷ CS14 ∷ []) (CS14 ∷ Toff012 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb0-1-4-3 ∷ []) (refl) ▸
       at 3 2 (Toff423 ∷ Toff012 ∷ []) (lem-auto-TOFF012-∣-TOFF324-at3443 c4) ▸
       at 5 1 (CS14⁻ ∷ []) (refl) ▸ done

  b1 : Chain (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Toff012 ∷ CS14⁻ ∷ []) (Sb0-1-23-4 ∷ Toff012 ∷ [])
  b1 = at 4 2 (CS14⁻ ∷ Toff012 ∷ []) (pw3 c4 (Toff012 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Toff012 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- F5 CS01 @1221: 8 steps
lem-F5-CS01-at1221 : Complete 4 → ⟪ (X4 ∷ Sb1-0-42-3 ∷ X4 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ []) ⟫ʷ
lem-F5-CS01-at1221 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb1-0-42-3 ∷ X4 ∷ Sb1-0-42-3 ∷ []) (CS02 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (X4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (X ↑)) ▸
       at 2 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ c4) ▸
       at 3 2 (X4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (X ↑)) ▸
       at 4 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ c4) ▸
       at 1 4 (CS01 ∷ []) (lem-F5-CS01 c4) ▸
       at 0 2 (CS02 ∷ Sw12 ∷ []) (lem-nat-1-CS01 c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- F5 CS01 @132132: 8 steps
lem-F5-CS01-at132132 : Complete 4 → ⟪ (X4 ∷ Sb1-0-43-2 ∷ X4 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ []) ⟫ʷ
lem-F5-CS01-at132132 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb1-0-43-2 ∷ X4 ∷ Sb1-0-43-2 ∷ []) (CS03 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (X4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (X)) ▸
       at 2 2 (Sb1-0-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·43·2⟩ c4) ▸
       at 3 2 (X4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (X)) ▸
       at 4 2 (Sb1-0-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·43·2⟩ c4) ▸
       at 1 4 (CS02 ∷ []) (lem-F5-CS01-at1221 c4) ▸
       at 0 2 (CS03 ∷ Sw23 ∷ []) (lem-nat-2-CS02 c4) ▸
       at 1 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- F5 CS01 @14213243: 8 steps
lem-F5-CS01-at14213243 : Complete 4 → ⟪ (X3 ∷ Sb1-0-34-2 ∷ X3 ∷ Sb1-0-34-2 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ []) ⟫ʷ
lem-F5-CS01-at14213243 c4 = run b0
  where
  b0 : Chain (X3 ∷ Sb1-0-34-2 ∷ X3 ∷ Sb1-0-34-2 ∷ []) (CS04 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (X4 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ X3 ∷ []) (X4 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb1-0-43-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·0·34·2⟩ c4) ▸
       at 3 2 (X4 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ X3 ∷ []) (X4 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sb1-0-43-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·0·34·2⟩ c4) ▸
       at 1 4 (CS03 ∷ []) (lem-F5-CS01-at132132 c4) ▸
       at 0 2 (CS04 ∷ Sw34 ∷ []) (lem-nat-3-CS03 c4) ▸
       at 1 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- F5 CS01 @142142: 8 steps
lem-F5-CS01-at142142 : Complete 4 → ⟪ (X2 ∷ Sb1-0-24-3 ∷ X2 ∷ Sb1-0-24-3 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ []) ⟫ʷ
lem-F5-CS01-at142142 c4 = run b0
  where
  b0 : Chain (X2 ∷ Sb1-0-24-3 ∷ X2 ∷ Sb1-0-24-3 ∷ []) (CS04 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (X3 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ X2 ∷ []) (X3 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb1-0-34-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·24·3⟩ c4) ▸
       at 3 2 (X3 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ X2 ∷ []) (X3 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sb1-0-34-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·24·3⟩ c4) ▸
       at 1 4 (CS04 ∷ []) (lem-F5-CS01-at14213243 c4) ▸
       at 0 2 (CS04 ∷ Sw23 ∷ []) (lem-nat-2-CS04 c4) ▸
       at 1 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- F5 CS01 @1441: 8 steps
lem-F5-CS01-at1441 : Complete 4 → ⟪ (X1 ∷ Sb2-0-14-3 ∷ X1 ∷ Sb2-0-14-3 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ []) ⟫ʷ
lem-F5-CS01-at1441 c4 = run b0
  where
  b0 : Chain (X1 ∷ Sb2-0-14-3 ∷ X1 ∷ Sb2-0-14-3 ∷ []) (CS04 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (X2 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ X1 ∷ []) (X2 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb1-0-24-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·14·3⟩ c4) ▸
       at 3 2 (X2 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ X1 ∷ []) (X2 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sb1-0-24-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·14·3⟩ c4) ▸
       at 1 4 (CS04 ∷ []) (lem-F5-CS01-at142142 c4) ▸
       at 0 2 (CS04 ∷ Sw12 ∷ []) (lem-nat-1-CS04 c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- SBsym @1221: 5 steps
lem-SBsym-at1221 : Complete 4 → ⟪ (Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-24-3 ∷ []) ⟫ʷ
lem-SBsym-at1221 c4 = run b0
  where
  b0 : Chain (Sb1-0-42-3 ∷ []) (Sb1-0-24-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ c4) ▸
       at 1 1 (Sb2-0-14-3 ∷ []) (lem-SBsym c4) ▸
       at 0 2 (Sb1-0-24-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·14·3⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- SBsym @132132: 5 steps
lem-SBsym-at132132 : Complete 4 → ⟪ (Sb1-0-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-34-2 ∷ []) ⟫ʷ
lem-SBsym-at132132 c4 = run b0
  where
  b0 : Chain (Sb1-0-43-2 ∷ []) (Sb1-0-34-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·43·2⟩ c4) ▸
       at 1 1 (Sb1-0-24-3 ∷ []) (lem-SBsym-at1221 c4) ▸
       at 0 2 (Sb1-0-34-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·24·3⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- SBsym @14213243: 5 steps
lem-SBsym-at14213243 : Complete 4 → ⟪ (Sb1-0-34-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-43-2 ∷ []) ⟫ʷ
lem-SBsym-at14213243 c4 = run b0
  where
  b0 : Chain (Sb1-0-34-2 ∷ []) (Sb1-0-43-2 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb1-0-43-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·0·34·2⟩ c4) ▸
       at 1 1 (Sb1-0-34-2 ∷ []) (lem-SBsym-at132132 c4) ▸
       at 0 2 (Sb1-0-43-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·0·34·2⟩ c4) ▸
       at 1 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- SBsym @142142: 5 steps
lem-SBsym-at142142 : Complete 4 → ⟪ (Sb1-0-24-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ []) ⟫ʷ
lem-SBsym-at142142 c4 = run b0
  where
  b0 : Chain (Sb1-0-24-3 ∷ []) (Sb1-0-42-3 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb1-0-34-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·24·3⟩ c4) ▸
       at 1 1 (Sb1-0-43-2 ∷ []) (lem-SBsym-at14213243 c4) ▸
       at 0 2 (Sb1-0-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·43·2⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- SBsym @1441: 5 steps
lem-SBsym-at1441 : Complete 4 → ⟪ (Sb2-0-14-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ []) ⟫ʷ
lem-SBsym-at1441 c4 = run b0
  where
  b0 : Chain (Sb2-0-14-3 ∷ []) (Sb2-0-41-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb1-0-24-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·14·3⟩ c4) ▸
       at 1 1 (Sb1-0-42-3 ∷ []) (lem-SBsym-at142142 c4) ▸
       at 0 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- beta-T @3443: 8 steps
lem-beta-T-at3443 : Complete 4 → ⟪ (Bx0-1243 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) ⟫ʷ
lem-beta-T-at3443 c4 = run b0
  where
  b0 : Chain (Bx0-1243 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1243⟩ c4) ▸
       at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-beta-T c4) ▸
       at 0 2 (Toff012 ∷ Sw34 ∷ []) (sym (c₃ (Toff) (Swap))) ▸
       at 1 2 (CCZ034 ∷ Sw34 ∷ []) (lem-nat-3-CCZ034 c4) ▸
       at 2 2 (Toff012 ∷ Sw34 ∷ []) (sym (c₃ (Toff) (Swap))) ▸
       at 3 2 (CCZ034 ∷ Sw34 ∷ []) (lem-nat-3-CCZ034 c4) ▸
       at 4 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- beta-T @01103443: 8 steps
lem-beta-T-at01103443 : Complete 4 → ⟪ (Bx1-0243 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CCZ134 ∷ Toff102 ∷ CCZ134 ∷ []) ⟫ʷ
lem-beta-T-at01103443 c4 = run b0
  where
  b0 : Chain (Bx1-0243 ∷ []) (Toff102 ∷ CCZ134 ∷ Toff102 ∷ CCZ134 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1243 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0243⟩ c4) ▸
       at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-beta-T-at3443 c4) ▸
       at 0 2 (Toff102 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff012 ∷ []) (Toff102 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 2 2 (Toff102 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff012 ∷ []) (Toff102 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 4 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- beta-T @0210213443: 8 steps
lem-beta-T-at0210213443 : Complete 4 → ⟪ (Bx2-0143 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) ⟫ʷ
lem-beta-T-at0210213443 c4 = run b0
  where
  b0 : Chain (Bx2-0143 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0243 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0143⟩ c4) ▸
       at 1 1 (Toff102 ∷ CCZ134 ∷ Toff102 ∷ CCZ134 ∷ []) (lem-beta-T-at01103443 c4) ▸
       at 0 2 (Toff201 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff102 ∷ []) (Toff201 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ134 ∷ []) (CCZ234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff201 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff102 ∷ []) (Toff201 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ134 ∷ []) (CCZ234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;2;3) | SBOX(0;1;43;2) @2332: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at2332 : Complete 4 → ⟪ (Sb⁻0-1-3-2 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ Sb⁻0-1-3-2 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-3-2 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ Sb⁻0-1-3-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·3·2⟩ c4) ▸
       at 2 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ c4) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sb⁻0-1-2-3 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩ c4) ▸
       at 0 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ c4) ▸
       at 1 2 (Sb⁻0-1-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·2·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;2;3) | SBOX(0;1;43;2) @01102332: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at01102332 : Complete 4 → ⟪ (Sb⁻1-0-3-2 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ Sb⁻1-0-3-2 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at01102332 c4 = run b0
  where
  b0 : Chain (Sb⁻1-0-3-2 ∷ Sb1-0-42-3 ∷ []) (Sb1-0-42-3 ∷ Sb⁻1-0-3-2 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·3·2⟩ c4) ▸
       at 2 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ c4) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sb⁻0-1-3-2 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at2332 c4) ▸
       at 0 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ c4) ▸
       at 1 2 (Sb⁻1-0-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·3·2⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;2;3) | SBOX(0;1;43;2) @02102331: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at02102331 : Complete 4 → ⟪ (Sb⁻2-0-3-1 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ Sb⁻2-0-3-1 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at02102331 c4 = run b0
  where
  b0 : Chain (Sb⁻2-0-3-1 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ Sb⁻2-0-3-1 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·3·1⟩ c4) ▸
       at 2 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ c4) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sb⁻1-0-3-2 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at01102332 c4) ▸
       at 0 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ c4) ▸
       at 1 2 (Sb⁻2-0-3-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·0·3·2⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto Kd0 | SBOX(1;2;34;0) @3443: 7 steps
lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩-at3443 : Complete 4 → ⟪ (K0⁻ ∷ Sb1-2-43-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-43-0 ∷ K0⁻ ∷ []) ⟫ʷ
lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩-at3443 c4 = run b0
  where
  b0 : Chain (K0⁻ ∷ Sb1-2-43-0 ∷ []) (Sb1-2-43-0 ∷ K0⁻ ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (K0⁻ ∷ Sw34 ∷ []) (sym (c₁ (K • iI) (Swap ↑ ↑))) ▸
       at 2 2 (Sb1-2-34-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·2·43·0⟩ c4) ▸
       at 1 2 (Sb1-2-34-0 ∷ K0⁻ ∷ []) (lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩ c4) ▸
       at 0 2 (Sb1-2-43-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·2·34·0⟩ c4) ▸
       at 1 2 (K0⁻ ∷ Sw34 ∷ []) (sym (c₁ (K • iI) (Swap ↑ ↑))) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto Kd0 | SBOX(1;2;34;0) @01103443: 7 steps
lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩-at01103443 : Complete 4 → ⟪ (K1⁻ ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ K1⁻ ∷ []) ⟫ʷ
lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩-at01103443 c4 = run b0
  where
  b0 : Chain (K1⁻ ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ K1⁻ ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (K0⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ K1⁻ ∷ []) (K0⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb1-2-43-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·2·43·1⟩ c4) ▸
       at 1 2 (Sb1-2-43-0 ∷ K0⁻ ∷ []) (lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩-at3443 c4) ▸
       at 0 2 (Sb0-2-43-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·2·43·0⟩ c4) ▸
       at 1 2 (K1⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ K0⁻ ∷ []) (K1⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto Kd0 | SBOX(1;2;34;0) @0210213443: 7 steps
lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩-at0210213443 : Complete 4 → ⟪ (K2⁻ ∷ Sb0-1-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-43-2 ∷ K2⁻ ∷ []) ⟫ʷ
lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩-at0210213443 c4 = run b0
  where
  b0 : Chain (K2⁻ ∷ Sb0-1-43-2 ∷ []) (Sb0-1-43-2 ∷ K2⁻ ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (K1⁻ ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ K2⁻ ∷ []) (K1⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ c4) ▸
       at 1 2 (Sb0-2-43-1 ∷ K1⁻ ∷ []) (lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩-at01103443 c4) ▸
       at 0 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ c4) ▸
       at 1 2 (K2⁻ ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ K1⁻ ∷ []) (K2⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto Kd0 | SBOX(1;2;34;0) @0310213442: 7 steps
lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩-at0310213442 : Complete 4 → ⟪ (K3⁻ ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ K3⁻ ∷ []) ⟫ʷ
lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩-at0310213442 c4 = run b0
  where
  b0 : Chain (K3⁻ ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ K3⁻ ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (K2⁻ ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ K3⁻ ∷ []) (K2⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ c4) ▸
       at 1 2 (Sb0-1-43-2 ∷ K2⁻ ∷ []) (lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩-at0210213443 c4) ▸
       at 0 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ c4) ▸
       at 1 2 (K3⁻ ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ K2⁻ ∷ []) (K3⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto Kd0 | SBOX(1;2;34;0) @03203442: 7 steps
lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩-at03203442 : Complete 4 → ⟪ (K3⁻ ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ K3⁻ ∷ []) ⟫ʷ
lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩-at03203442 c4 = run b0
  where
  b0 : Chain (K3⁻ ∷ Sb1-0-42-3 ∷ []) (Sb1-0-42-3 ∷ K3⁻ ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (K3⁻ ∷ Sw01 ∷ []) (c₂ (Swap) ((K • iI) ↑)) ▸
       at 2 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ c4) ▸
       at 1 2 (Sb0-1-42-3 ∷ K3⁻ ∷ []) (lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩-at0310213442 c4) ▸
       at 0 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ c4) ▸
       at 1 2 (K3⁻ ∷ Sw01 ∷ []) (c₂ (Swap) ((K • iI) ↑)) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto Kd0 | SBOX(1;2;34;0) @0312203441: 7 steps
lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩-at0312203441 : Complete 4 → ⟪ (K3⁻ ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ K3⁻ ∷ []) ⟫ʷ
lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩-at0312203441 c4 = run b0
  where
  b0 : Chain (K3⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ K3⁻ ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (K3⁻ ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K • iI)) ▸
       at 2 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ c4) ▸
       at 1 2 (Sb1-0-42-3 ∷ K3⁻ ∷ []) (lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩-at03203442 c4) ▸
       at 0 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ c4) ▸
       at 1 2 (K3⁻ ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K • iI)) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CS01 | SBOX(2;3;04;1) @0110: 7 steps
lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at0110 : Complete 4 → ⟪ (CS01 ∷ Sb2-3-14-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-14-0 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at0110 c4 = run b0
  where
  b0 : Chain (CS01 ∷ Sb2-3-14-0 ∷ []) (Sb2-3-14-0 ∷ CS01 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS01 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS01 ∷ []) (CS01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb2-3-04-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·3·14·0⟩ c4) ▸
       at 1 2 (Sb2-3-04-1 ∷ CS01 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩ c4) ▸
       at 0 2 (Sb2-3-14-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·3·04·1⟩ c4) ▸
       at 1 2 (CS01 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS01 ∷ []) (CS01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CS01 | SBOX(2;3;04;1) @021021: 7 steps
lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at021021 : Complete 4 → ⟪ (CS02 ∷ Sb1-3-24-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-3-24-0 ∷ CS02 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at021021 c4 = run b0
  where
  b0 : Chain (CS02 ∷ Sb1-3-24-0 ∷ []) (Sb1-3-24-0 ∷ CS02 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS01 ∷ Sw12 ∷ []) (lem-nat-1-CS02 c4) ▸
       at 2 2 (Sb2-3-14-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·3·24·0⟩ c4) ▸
       at 1 2 (Sb2-3-14-0 ∷ CS01 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at0110 c4) ▸
       at 0 2 (Sb1-3-24-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·3·14·0⟩ c4) ▸
       at 1 2 (CS02 ∷ Sw12 ∷ []) (lem-nat-1-CS01 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CS01 | SBOX(2;3;04;1) @03102132: 7 steps
lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at03102132 : Complete 4 → ⟪ (CS03 ∷ Sb1-2-34-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-34-0 ∷ CS03 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at03102132 c4 = run b0
  where
  b0 : Chain (CS03 ∷ Sb1-2-34-0 ∷ []) (Sb1-2-34-0 ∷ CS03 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS02 ∷ Sw23 ∷ []) (lem-nat-2-CS03 c4) ▸
       at 2 2 (Sb1-3-24-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·2·34·0⟩ c4) ▸
       at 1 2 (Sb1-3-24-0 ∷ CS02 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at021021 c4) ▸
       at 0 2 (Sb1-2-34-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·3·24·0⟩ c4) ▸
       at 1 2 (CS03 ∷ Sw23 ∷ []) (lem-nat-2-CS02 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CS01 | SBOX(2;3;04;1) @0410213243: 7 steps
lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at0410213243 : Complete 4 → ⟪ (CS04 ∷ Sb1-2-43-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-43-0 ∷ CS04 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at0410213243 c4 = run b0
  where
  b0 : Chain (CS04 ∷ Sb1-2-43-0 ∷ []) (Sb1-2-43-0 ∷ CS04 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS03 ∷ Sw34 ∷ []) (lem-nat-3-CS04 c4) ▸
       at 2 2 (Sb1-2-34-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·2·43·0⟩ c4) ▸
       at 1 2 (Sb1-2-34-0 ∷ CS03 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at03102132 c4) ▸
       at 0 2 (Sb1-2-43-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·2·34·0⟩ c4) ▸
       at 1 2 (CS04 ∷ Sw34 ∷ []) (lem-nat-3-CS03 c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CS01 | SBOX(2;3;04;1) @04203243: 7 steps
lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at04203243 : Complete 4 → ⟪ (CS14 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ CS14 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at04203243 c4 = run b0
  where
  b0 : Chain (CS14 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ CS14 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS04 ∷ Sw01 ∷ []) (lem-nat-0-CS14 c4) ▸
       at 2 2 (Sb1-2-43-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·2·43·1⟩ c4) ▸
       at 1 2 (Sb1-2-43-0 ∷ CS04 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at0410213243 c4) ▸
       at 0 2 (Sb0-2-43-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·2·43·0⟩ c4) ▸
       at 1 2 (CS14 ∷ Sw01 ∷ []) (lem-nat-0-CS04 c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CS01 | SBOX(2;3;04;1) @0412203143: 7 steps
lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at0412203143 : Complete 4 → ⟪ (CS24 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-43-2 ∷ CS24 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at0412203143 c4 = run b0
  where
  b0 : Chain (CS24 ∷ Sb0-1-43-2 ∷ []) (Sb0-1-43-2 ∷ CS24 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS14 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS24 ∷ []) (CS14 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ c4) ▸
       at 1 2 (Sb0-2-43-1 ∷ CS14 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at04203243 c4) ▸
       at 0 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ c4) ▸
       at 1 2 (CS24 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS14 ∷ []) (CS24 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CS01 | SBOX(2;3;04;1) @0413203142: 7 steps
lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at0413203142 : Complete 4 → ⟪ (CS34 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CS34 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at0413203142 c4 = run b0
  where
  b0 : Chain (CS34 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ CS34 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS24 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS34 ∷ []) (CS24 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ c4) ▸
       at 1 2 (Sb0-1-43-2 ∷ CS24 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at0412203143 c4) ▸
       at 0 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ c4) ▸
       at 1 2 (CS34 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS24 ∷ []) (CS34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CS01 | SBOX(2;3;04;1) @0413213042: 7 steps
lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at0413213042 : Complete 4 → ⟪ (CS34 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ CS34 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at0413213042 c4 = run b0
  where
  b0 : Chain (CS34 ∷ Sb1-0-42-3 ∷ []) (Sb1-0-42-3 ∷ CS34 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS34 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑)) ▸
       at 2 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ c4) ▸
       at 1 2 (Sb0-1-42-3 ∷ CS34 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at0413203142 c4) ▸
       at 0 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ c4) ▸
       at 1 2 (CS34 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑)) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CS01 | SBOX(2;3;04;1) @04133041: 7 steps
lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at04133041 : Complete 4 → ⟪ (CS34 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CS34 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at04133041 c4 = run b0
  where
  b0 : Chain (CS34 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CS34 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸
       at 2 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ c4) ▸
       at 1 2 (Sb1-0-42-3 ∷ CS34 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at0413213042 c4) ▸
       at 0 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ c4) ▸
       at 1 2 (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym34 @243243: 5 steps
lem-sym34-at243243 : Complete 4 → ⟪ (Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ []) ⟫ʷ
lem-sym34-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ []) (Bx0-1432 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ c4) ▸
       at 1 1 (Bx0-1342 ∷ []) (lem-sym34-at2332 c4) ▸
       at 0 2 (Bx0-1432 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1342⟩ c4) ▸
       at 1 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym34 @0110243243: 5 steps
lem-sym34-at0110243243 : Complete 4 → ⟪ (Bx1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0432 ∷ []) ⟫ʷ
lem-sym34-at0110243243 c4 = run b0
  where
  b0 : Chain (Bx1-0423 ∷ []) (Bx1-0432 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ c4) ▸
       at 1 1 (Bx0-1432 ∷ []) (lem-sym34-at243243 c4) ▸
       at 0 2 (Bx1-0432 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1432⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym34 @0210243143: 5 steps
lem-sym34-at0210243143 : Complete 4 → ⟪ (Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0431 ∷ []) ⟫ʷ
lem-sym34-at0210243143 c4 = run b0
  where
  b0 : Chain (Bx2-0413 ∷ []) (Bx2-0431 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ c4) ▸
       at 1 1 (Bx1-0432 ∷ []) (lem-sym34-at0110243243 c4) ▸
       at 0 2 (Bx2-0431 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0432⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @2442: 5 steps
lem-sym23-at2442 : Complete 4 → ⟪ (Bx0-1432 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1342 ∷ []) ⟫ʷ
lem-sym23-at2442 c4 = run b0
  where
  b0 : Chain (Bx0-1432 ∷ []) (Bx0-1342 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1423 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1432⟩ c4) ▸
       at 1 1 (Bx0-1243 ∷ []) (lem-sym23-at243243 c4) ▸
       at 0 2 (Bx0-1342 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1243⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @01102442: 5 steps
lem-sym23-at01102442 : Complete 4 → ⟪ (Bx1-0432 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0342 ∷ []) ⟫ʷ
lem-sym23-at01102442 c4 = run b0
  where
  b0 : Chain (Bx1-0432 ∷ []) (Bx1-0342 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1432 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0432⟩ c4) ▸
       at 1 1 (Bx0-1342 ∷ []) (lem-sym23-at2442 c4) ▸
       at 0 2 (Bx1-0342 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1342⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @02102441: 5 steps
lem-sym23-at02102441 : Complete 4 → ⟪ (Bx2-0431 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0341 ∷ []) ⟫ʷ
lem-sym23-at02102441 c4 = run b0
  where
  b0 : Chain (Bx2-0431 ∷ []) (Bx2-0341 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0432 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0431⟩ c4) ▸
       at 1 1 (Bx1-0342 ∷ []) (lem-sym23-at01102442 c4) ▸
       at 0 2 (Bx2-0341 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0342⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- beta-T @233442: 8 steps
lem-beta-T-at233442 : Complete 4 → ⟪ (Bx0-1342 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) ⟫ʷ
lem-beta-T-at233442 c4 = run b0
  where
  b0 : Chain (Bx0-1342 ∷ []) (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1243 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1342⟩ c4) ▸
       at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-beta-T-at3443 c4) ▸
       at 0 2 (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 c4) ▸
       at 1 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 2 2 (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 c4) ▸
       at 3 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 4 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- beta-T @0110233442: 8 steps
lem-beta-T-at0110233442 : Complete 4 → ⟪ (Bx1-0342 ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ CCZ124 ∷ Toff103 ∷ CCZ124 ∷ []) ⟫ʷ
lem-beta-T-at0110233442 c4 = run b0
  where
  b0 : Chain (Bx1-0342 ∷ []) (Toff103 ∷ CCZ124 ∷ Toff103 ∷ CCZ124 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1342 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0342⟩ c4) ▸
       at 1 1 (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-beta-T-at233442 c4) ▸
       at 0 2 (Toff103 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff013 ∷ []) (Toff103 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 2 2 (Toff103 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff013 ∷ []) (Toff103 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 4 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- beta-T @0210233441: 8 steps
lem-beta-T-at0210233441 : Complete 4 → ⟪ (Bx2-0341 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) ⟫ʷ
lem-beta-T-at0210233441 c4 = run b0
  where
  b0 : Chain (Bx2-0341 ∷ []) (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0342 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0341⟩ c4) ▸
       at 1 1 (Toff103 ∷ CCZ124 ∷ Toff103 ∷ CCZ124 ∷ []) (lem-beta-T-at0110233442 c4) ▸
       at 0 2 (Toff203 ∷ Sw12 ∷ []) (lem-nat-1-TOFF103 c4) ▸
       at 1 2 (CCZ124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff203 ∷ Sw12 ∷ []) (lem-nat-1-TOFF103 c4) ▸
       at 3 2 (CCZ124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @233442: 5 steps
lem-sym23-at233442 : Complete 4 → ⟪ (Bx0-1342 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ []) ⟫ʷ
lem-sym23-at233442 c4 = run b0
  where
  b0 : Chain (Bx0-1342 ∷ []) (Bx0-1432 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1243 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1342⟩ c4) ▸
       at 1 1 (Bx0-1423 ∷ []) (lem-sym23-at3443 c4) ▸
       at 0 2 (Bx0-1432 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1423⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @0110233442: 5 steps
lem-sym23-at0110233442 : Complete 4 → ⟪ (Bx1-0342 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0432 ∷ []) ⟫ʷ
lem-sym23-at0110233442 c4 = run b0
  where
  b0 : Chain (Bx1-0342 ∷ []) (Bx1-0432 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1342 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0342⟩ c4) ▸
       at 1 1 (Bx0-1432 ∷ []) (lem-sym23-at233442 c4) ▸
       at 0 2 (Bx1-0432 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1432⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @0210233441: 5 steps
lem-sym23-at0210233441 : Complete 4 → ⟪ (Bx2-0341 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0431 ∷ []) ⟫ʷ
lem-sym23-at0210233441 c4 = run b0
  where
  b0 : Chain (Bx2-0341 ∷ []) (Bx2-0431 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0342 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0341⟩ c4) ▸
       at 1 1 (Bx1-0432 ∷ []) (lem-sym23-at0110233442 c4) ▸
       at 0 2 (Bx2-0431 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0432⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym34 @2442: 5 steps
lem-sym34-at2442 : Complete 4 → ⟪ (Bx0-1432 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ []) ⟫ʷ
lem-sym34-at2442 c4 = run b0
  where
  b0 : Chain (Bx0-1432 ∷ []) (Bx0-1423 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1423 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1432⟩ c4) ▸
       at 1 1 (Bx0-1432 ∷ []) (lem-sym34-at243243 c4) ▸
       at 0 2 (Bx0-1423 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1432⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym34 @01102442: 5 steps
lem-sym34-at01102442 : Complete 4 → ⟪ (Bx1-0432 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ []) ⟫ʷ
lem-sym34-at01102442 c4 = run b0
  where
  b0 : Chain (Bx1-0432 ∷ []) (Bx1-0423 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1432 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0432⟩ c4) ▸
       at 1 1 (Bx0-1423 ∷ []) (lem-sym34-at2442 c4) ▸
       at 0 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym34 @02102441: 5 steps
lem-sym34-at02102441 : Complete 4 → ⟪ (Bx2-0431 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ []) ⟫ʷ
lem-sym34-at02102441 c4 = run b0
  where
  b0 : Chain (Bx2-0431 ∷ []) (Bx2-0413 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0432 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0431⟩ c4) ▸
       at 1 1 (Bx1-0423 ∷ []) (lem-sym34-at01102442 c4) ▸
       at 0 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto K0 | SBOX(1;2;34;0) @3443: 7 steps
lem-auto-K0-∣-SBOX⟨1·2·34·0⟩-at3443 : Complete 4 → ⟪ (K0 ∷ Sb1-2-43-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-43-0 ∷ K0 ∷ []) ⟫ʷ
lem-auto-K0-∣-SBOX⟨1·2·34·0⟩-at3443 c4 = run b0
  where
  b0 : Chain (K0 ∷ Sb1-2-43-0 ∷ []) (Sb1-2-43-0 ∷ K0 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 2 2 (Sb1-2-34-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·2·43·0⟩ c4) ▸
       at 1 2 (Sb1-2-34-0 ∷ K0 ∷ []) (lem-auto-K0-∣-SBOX⟨1·2·34·0⟩ c4) ▸
       at 0 2 (Sb1-2-43-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·2·34·0⟩ c4) ▸
       at 1 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto K0 | SBOX(1;2;34;0) @01103443: 7 steps
lem-auto-K0-∣-SBOX⟨1·2·34·0⟩-at01103443 : Complete 4 → ⟪ (K1 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ K1 ∷ []) ⟫ʷ
lem-auto-K0-∣-SBOX⟨1·2·34·0⟩-at01103443 c4 = run b0
  where
  b0 : Chain (K1 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ K1 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (K0 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ K1 ∷ []) (K0 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb1-2-43-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·2·43·1⟩ c4) ▸
       at 1 2 (Sb1-2-43-0 ∷ K0 ∷ []) (lem-auto-K0-∣-SBOX⟨1·2·34·0⟩-at3443 c4) ▸
       at 0 2 (Sb0-2-43-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·2·43·0⟩ c4) ▸
       at 1 2 (K1 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ K0 ∷ []) (K1 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto K0 | SBOX(1;2;34;0) @0210213443: 7 steps
lem-auto-K0-∣-SBOX⟨1·2·34·0⟩-at0210213443 : Complete 4 → ⟪ (K2 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-43-2 ∷ K2 ∷ []) ⟫ʷ
lem-auto-K0-∣-SBOX⟨1·2·34·0⟩-at0210213443 c4 = run b0
  where
  b0 : Chain (K2 ∷ Sb0-1-43-2 ∷ []) (Sb0-1-43-2 ∷ K2 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (K1 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ K2 ∷ []) (K1 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ c4) ▸
       at 1 2 (Sb0-2-43-1 ∷ K1 ∷ []) (lem-auto-K0-∣-SBOX⟨1·2·34·0⟩-at01103443 c4) ▸
       at 0 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ c4) ▸
       at 1 2 (K2 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ K1 ∷ []) (K2 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto K0 | SBOX(1;2;34;0) @0310213442: 7 steps
lem-auto-K0-∣-SBOX⟨1·2·34·0⟩-at0310213442 : Complete 4 → ⟪ (K3 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ K3 ∷ []) ⟫ʷ
lem-auto-K0-∣-SBOX⟨1·2·34·0⟩-at0310213442 c4 = run b0
  where
  b0 : Chain (K3 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ K3 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (K2 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ K3 ∷ []) (K2 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ c4) ▸
       at 1 2 (Sb0-1-43-2 ∷ K2 ∷ []) (lem-auto-K0-∣-SBOX⟨1·2·34·0⟩-at0210213443 c4) ▸
       at 0 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ c4) ▸
       at 1 2 (K3 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ K2 ∷ []) (K3 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto K0 | SBOX(1;2;34;0) @03203442: 7 steps
lem-auto-K0-∣-SBOX⟨1·2·34·0⟩-at03203442 : Complete 4 → ⟪ (K3 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ K3 ∷ []) ⟫ʷ
lem-auto-K0-∣-SBOX⟨1·2·34·0⟩-at03203442 c4 = run b0
  where
  b0 : Chain (K3 ∷ Sb1-0-42-3 ∷ []) (Sb1-0-42-3 ∷ K3 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (K3 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑)) ▸
       at 2 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ c4) ▸
       at 1 2 (Sb0-1-42-3 ∷ K3 ∷ []) (lem-auto-K0-∣-SBOX⟨1·2·34·0⟩-at0310213442 c4) ▸
       at 0 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ c4) ▸
       at 1 2 (K3 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑)) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D174 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0001 ; wl0002 ; wl0003 ; wl0006 ; wl0007 ; wl0012 ; wl0016 ; wl0019 ; wl0022 ; wl0024 ; wl0025 ; wl0031 ; wl0043 ; wl0046 ; wl0056 ; wl0061 ; wl0062 ; wl0076 ; wl0103 ; wl0121 ; wl0190 ; wl0257 ; wl0306 ; wl0307 ; wl0308 ; wl0597 ; wl0598 ; wp0370 ; wp0371 ; wp0372)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-beta-T-at14213243 ; lem-sym34 ; lem-sym34-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS21-at2332 ; lem-sym23-at243243 ; lem-sym23-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-SBsym-at0113203442 ; lem-auto-BOX⟨0·1234⟩-∣-K0 ; lem-auto-BOX⟨0·1234⟩-∣-Kd0 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CS24-at2332 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CS41-at2332 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd41-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-CS20-beta-c-at243243 ; lem-CS20-beta-ci-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D089 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-CX24-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D161 using (lem-auto-BOX⟨0·1234⟩-∣-CSd24)
open import Examples.Groups.Clifford+CS.Five.D.D173 using (lem-auto-BOX⟨0·1234⟩-∣-CSd02)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-nat-1-CCZ023 ; lem-nat-1-TOFF014 ; lem-nat-2-BOX⟨0·1234⟩ ; lem-nat-2-BOX⟨0·1324⟩ ; lem-nat-3-BOX⟨0·1423⟩)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-CCZ013 ; lem-nat-2-CCZ124 ; lem-nat-2-CCZ134 ; lem-nat-3-BOX⟨0·1324⟩)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-BOX⟨0·1423⟩ ; lem-nat-0-BOX⟨1·0423⟩ ; lem-nat-1-BOX⟨1·0423⟩ ; lem-nat-1-BOX⟨2·0413⟩ ; lem-nat-3-CCZ123 ; lem-nat-3-CCZ124)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-0-SBOX⟨0·1·42·3⟩ ; lem-nat-0-SBOX⟨1·0·42·3⟩ ; lem-nat-1-SBOX⟨1·0·42·3⟩ ; lem-nat-1-SBOX⟨2·0·41·3⟩ ; lem-nat-2-CSd02 ; lem-nat-2-SBOX⟨0·1·23·4⟩ ; lem-nat-2-SBOX⟨0·1·32·4⟩ ; lem-nat-3-SBOX⟨0·1·32·4⟩ ; lem-nat-3-SBOX⟨0·1·42·3⟩)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-2-CS04 ; lem-nat-2-CSd04 ; lem-nat-3-CS04 ; lem-nat-3-CSd04)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-2-CSd03 ; lem-nat-3-CS03 ; lem-nat-3-CSd03)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-nat-1-BOX⟨0·4213⟩)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-0-SBOX⟨0·2·3·1⟩ ; lem-nat-0-SBOX⟨1·2·3·0⟩ ; lem-nat-0-SBOXd⟨0·2·3·1⟩ ; lem-nat-0-SBOXd⟨1·2·3·0⟩)
open import Examples.Groups.Clifford+CS.Five.D.R017 using (lem-nat-1-SBOX⟨0·1·3·2⟩ ; lem-nat-1-SBOX⟨0·2·3·1⟩ ; lem-nat-1-SBOXd⟨0·1·3·2⟩ ; lem-nat-1-SBOXd⟨0·2·3·1⟩ ; lem-nat-2-SBOX⟨1·2·4·0⟩ ; lem-nat-2-SBOX⟨1·3·4·0⟩ ; lem-nat-2-SBOXd⟨1·2·4·0⟩ ; lem-nat-2-SBOXd⟨1·3·4·0⟩ ; lem-nat-3-SBOX⟨1·2·3·0⟩ ; lem-nat-3-SBOX⟨1·2·4·0⟩ ; lem-nat-3-SBOXd⟨1·2·3·0⟩ ; lem-nat-3-SBOXd⟨1·2·4·0⟩)
-- auto SBOX(0;1;23;4) | CSd02: 11 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd02 : Ws → ⟪ (Sb0-1-23-4 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd02 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-23-4 ∷ CS02⁻ ∷ []) (Bx0-1234 ∷ Toff423 ∷ CS02⁻ ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 1 (CS14⁻ ∷ []) (refl) ▸
       at 4 2 (CS02⁻ ∷ CS14⁻ ∷ []) (sym (wp0370 c4)) ▸
       at 5 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 3 2 (CS02⁻ ∷ Toff423 ∷ []) (sym (wp0371 c4)) ▸
       at 2 1 (CS14 ∷ []) (refl) ▸
       at 2 2 (CS02⁻ ∷ CS14 ∷ []) (sym (wp0372 c4)) ▸
       at 3 1 (Sb0-1-4-3 ∷ []) (refl) ▸ done

  b1 : Chain (Bx0-1234 ∷ Toff423 ∷ CS02⁻ ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (CS02⁻ ∷ Sb0-1-23-4 ∷ [])
  b1 = at 1 2 (CS02⁻ ∷ Toff423 ∷ []) (sym (wp0371 c4)) ▸
       at 0 2 (CS02⁻ ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd02 c4) ▸
       at 1 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- auto SBOX(0;1;23;4) | CSd02 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd02-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd02-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 (CS02⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd03 (lit c4)) ▸
       at 1 2 (CS02⁻ ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd02 c4) ▸
       at 0 2 (CS03⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd02 (lit c4)) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto BOX(0;1234) | CS04: 5 steps
lem-auto-BOX⟨0·1234⟩-∣-CS04 : Ws → ⟪ (Bx0-1234 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS04 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CS04 ∷ []) (CS04 ∷ Bx0-1234 ∷ [])
  b0 = at 0 1 (Bx0-1243 ∷ []) (lem-sym34 c4) ▸
       at 0 1 (Bx0-1423 ∷ []) (lem-sym23-at3443 c4) ▸
       at 0 2 (CS04 ∷ Bx0-1423 ∷ []) (sym (lem-CS20-beta-c-at243243 c4)) ▸
       at 1 1 (Bx0-1243 ∷ []) (lem-sym23-at243243 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym34-at3443 c4) ▸ done


-- auto BOX(0;1234) | CSd04: 5 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd04 : Ws → ⟪ (Bx0-1234 ∷ CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS04⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd04 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ Bx0-1234 ∷ [])
  b0 = at 0 1 (Bx0-1243 ∷ []) (lem-sym34 c4) ▸
       at 0 1 (Bx0-1423 ∷ []) (lem-sym23-at3443 c4) ▸
       at 0 2 (CS04⁻ ∷ Bx0-1423 ∷ []) (sym (lem-CS20-beta-ci-at243243 c4)) ▸
       at 1 1 (Bx0-1243 ∷ []) (lem-sym23-at243243 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym34-at3443 c4) ▸ done


-- beta-T @143143: 8 steps
lem-beta-T-at143143 : Ws → ⟪ (Bx0-4213 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) ⟫ʷ
lem-beta-T-at143143 c4 = run b0
  where
  b0 : Chain (Bx0-4213 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx0-4123 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·4213⟩ (lit c4)) ▸
       at 1 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at14213243 c4) ▸
       at 0 2 (Toff024 ∷ Sw12 ∷ []) (lem-nat-1-TOFF014 (lit c4)) ▸
       at 1 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 (lit c4)) ▸
       at 2 2 (Toff024 ∷ Sw12 ∷ []) (lem-nat-1-TOFF014 (lit c4)) ▸
       at 3 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 (lit c4)) ▸
       at 4 2 [] (wl0001 (lit c4)) ▸ done


-- auto BOX(0;1234) | CS04 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS04-at2332 : Ws → ⟪ (Bx0-1324 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS04-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ CS04 ∷ []) (CS04 ∷ Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ (lit c4)) ▸
       at 2 2 (CS04 ∷ Sw23 ∷ []) (lem-nat-2-CS04 (lit c4)) ▸
       at 1 2 (CS04 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS04 c4) ▸
       at 0 2 (CS04 ∷ Sw23 ∷ []) (lem-nat-2-CS04 (lit c4)) ▸
       at 1 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto BOX(0;1234) | CS04 @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS04-at243243 : Ws → ⟪ (Bx0-1423 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS04-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ CS03 ∷ []) (CS03 ∷ Bx0-1423 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ (lit c4)) ▸
       at 2 2 (CS04 ∷ Sw34 ∷ []) (lem-nat-3-CS03 (lit c4)) ▸
       at 1 2 (CS04 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS04-at2332 c4) ▸
       at 0 2 (CS03 ∷ Sw34 ∷ []) (lem-nat-3-CS04 (lit c4)) ▸
       at 1 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto BOX(0;1234) | CS04 @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS04-at0110243243 : Ws → ⟪ (Bx1-0423 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS04-at0110243243 c4 = run b0
  where
  b0 : Chain (Bx1-0423 ∷ CS13 ∷ []) (CS13 ∷ Bx1-0423 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 2 2 (CS03 ∷ Sw01 ∷ []) (sym (wl0019 (lit c4))) ▸
       at 1 2 (CS03 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS04-at243243 c4) ▸
       at 0 2 (CS13 ∷ Sw01 ∷ []) (sym (wl0061 (lit c4))) ▸
       at 1 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto BOX(0;1234) | CS04 @0210243143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS04-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS04-at0210243143 c4 = run b0
  where
  b0 : Chain (Bx2-0413 ∷ CS23 ∷ []) (CS23 ∷ Bx2-0413 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 2 2 (CS13 ∷ Sw12 ∷ []) (sym (wl0024 (lit c4))) ▸
       at 1 2 (CS13 ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS04-at0110243243 c4) ▸
       at 0 2 (CS23 ∷ Sw12 ∷ []) (sym (wl0025 (lit c4))) ▸
       at 1 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto BOX(0;1234) | K0 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-K0-at2332 : Ws → ⟪ (Bx0-1324 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-K0-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ K0 ∷ []) (K0 ∷ Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ (lit c4)) ▸
       at 2 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 1 2 (K0 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-K0 c4) ▸
       at 0 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 1 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto BOX(0;1234) | K0 @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-K0-at243243 : Ws → ⟪ (Bx0-1423 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-K0-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ K0 ∷ []) (K0 ∷ Bx0-1423 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ (lit c4)) ▸
       at 2 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 1 2 (K0 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-K0-at2332 c4) ▸
       at 0 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 1 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto BOX(0;1234) | K0 @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-K0-at0110243243 : Ws → ⟪ (Bx1-0423 ∷ K1 ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-K0-at0110243243 c4 = run b0
  where
  b0 : Chain (Bx1-0423 ∷ K1 ∷ []) (K1 ∷ Bx1-0423 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 2 2 (K0 ∷ Sw01 ∷ []) (sym (wl0031 (lit c4))) ▸
       at 1 2 (K0 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-K0-at243243 c4) ▸
       at 0 2 (K1 ∷ Sw01 ∷ []) (sym (wl0076 (lit c4))) ▸
       at 1 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto BOX(0;1234) | K0 @0210243143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-K0-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ K2 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-K0-at0210243143 c4 = run b0
  where
  b0 : Chain (Bx2-0413 ∷ K2 ∷ []) (K2 ∷ Bx2-0413 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 2 2 (K1 ∷ Sw12 ∷ []) (sym (wl0062 (lit c4))) ▸
       at 1 2 (K1 ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-K0-at0110243243 c4) ▸
       at 0 2 (K2 ∷ Sw12 ∷ []) (sym (wl0056 (lit c4))) ▸
       at 1 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto BOX(0;1234) | Kd0 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-Kd0-at2332 : Ws → ⟪ (Bx0-1324 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-Kd0-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ K0⁻ ∷ []) (K0⁻ ∷ Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ (lit c4)) ▸
       at 2 2 (K0⁻ ∷ Sw23 ∷ []) (sym (c₁ (K • iI) (Swap ↑))) ▸
       at 1 2 (K0⁻ ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-Kd0 c4) ▸
       at 0 2 (K0⁻ ∷ Sw23 ∷ []) (sym (c₁ (K • iI) (Swap ↑))) ▸
       at 1 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto BOX(0;1234) | Kd0 @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-Kd0-at243243 : Ws → ⟪ (Bx0-1423 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-Kd0-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ K0⁻ ∷ []) (K0⁻ ∷ Bx0-1423 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ (lit c4)) ▸
       at 2 2 (K0⁻ ∷ Sw34 ∷ []) (sym (c₁ (K • iI) (Swap ↑ ↑))) ▸
       at 1 2 (K0⁻ ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-Kd0-at2332 c4) ▸
       at 0 2 (K0⁻ ∷ Sw34 ∷ []) (sym (c₁ (K • iI) (Swap ↑ ↑))) ▸
       at 1 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto BOX(0;1234) | Kd0 @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-Kd0-at0110243243 : Ws → ⟪ (Bx1-0423 ∷ K1⁻ ∷ []) ⟫ʷ ≈ ⟪ (K1⁻ ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-Kd0-at0110243243 c4 = run b0
  where
  b0 : Chain (Bx1-0423 ∷ K1⁻ ∷ []) (K1⁻ ∷ Bx1-0423 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 2 2 (K0⁻ ∷ Sw01 ∷ []) (sym (wl0257 (lit c4))) ▸
       at 1 2 (K0⁻ ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-Kd0-at243243 c4) ▸
       at 0 2 (K1⁻ ∷ Sw01 ∷ []) (sym (wl0306 (lit c4))) ▸
       at 1 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto BOX(0;1234) | Kd0 @0210243143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-Kd0-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ K2⁻ ∷ []) ⟫ʷ ≈ ⟪ (K2⁻ ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-Kd0-at0210243143 c4 = run b0
  where
  b0 : Chain (Bx2-0413 ∷ K2⁻ ∷ []) (K2⁻ ∷ Bx2-0413 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 2 2 (K1⁻ ∷ Sw12 ∷ []) (sym (wl0307 (lit c4))) ▸
       at 1 2 (K1⁻ ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-Kd0-at0110243243 c4) ▸
       at 0 2 (K2⁻ ∷ Sw12 ∷ []) (sym (wl0308 (lit c4))) ▸
       at 1 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto BOX(0;1234) | CSd04 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd04-at2332 : Ws → ⟪ (Bx0-1324 ∷ CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS04⁻ ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd04-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ (lit c4)) ▸
       at 2 2 (CS04⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd04 (lit c4)) ▸
       at 1 2 (CS04⁻ ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd04 c4) ▸
       at 0 2 (CS04⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd04 (lit c4)) ▸
       at 1 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto BOX(0;1234) | CSd04 @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd04-at243243 : Ws → ⟪ (Bx0-1423 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd04-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Bx0-1423 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ (lit c4)) ▸
       at 2 2 (CS04⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd03 (lit c4)) ▸
       at 1 2 (CS04⁻ ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd04-at2332 c4) ▸
       at 0 2 (CS03⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd04 (lit c4)) ▸
       at 1 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto BOX(0;1234) | CSd04 @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd04-at0110243243 : Ws → ⟪ (Bx1-0423 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd04-at0110243243 c4 = run b0
  where
  b0 : Chain (Bx1-0423 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ Bx1-0423 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 2 2 (CS03⁻ ∷ Sw01 ∷ []) (sym (wl0022 (lit c4))) ▸
       at 1 2 (CS03⁻ ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd04-at243243 c4) ▸
       at 0 2 (CS13⁻ ∷ Sw01 ∷ []) (sym (wl0121 (lit c4))) ▸
       at 1 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto BOX(0;1234) | CSd04 @0210243143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd04-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd04-at0210243143 c4 = run b0
  where
  b0 : Chain (Bx2-0413 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Bx2-0413 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 2 2 (CS13⁻ ∷ Sw12 ∷ []) (sym (wl0043 (lit c4))) ▸
       at 1 2 (CS13⁻ ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd04-at0110243243 c4) ▸
       at 0 2 (CS23⁻ ∷ Sw12 ∷ []) (sym (wl0046 (lit c4))) ▸
       at 1 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | CCZ134: 9 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ134 : Ws → ⟪ (Sb0-1-23-4 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ134 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-23-4 ∷ CCZ134 ∷ []) (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 1 1 (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) (wl0190 (lit c4)) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS14 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS41-at2332 c4) ▸
       at 1 2 (CX34 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CX24-at2332 c4) ▸
       at 2 2 (CS14⁻ ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd41-at2332 c4) ▸
       at 3 2 (CX34 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CX24-at2332 c4) ▸
       at 4 2 (CS13 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS21-at2332 c4) ▸
       at 5 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸ done

  b1 : Chain (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ Sb0-1-23-4 ∷ []) (CCZ134 ∷ Sb0-1-23-4 ∷ [])
  b1 = at 0 5 (CCZ134 ∷ []) (sym (wl0190 (lit c4))) ▸ done


-- auto SBOX(0;1;23;4) | SBOX(1;3;4;0): 5 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·3·4·0⟩ : Ws → ⟪ (Sb0-1-23-4 ∷ Sb1-3-4-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-3-4-0 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·3·4·0⟩ c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ Sb1-3-4-0 ∷ []) (Sb1-3-4-0 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 1 1 (CS34 ∷ []) (refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS34 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS24-at2332 c4) ▸
       at 1 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 1 (Sb1-3-4-0 ∷ []) (refl) ▸ done


-- auto SBOX(0;1;23;4) | CSd24: 9 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd24 : Ws → ⟪ (Sb0-1-23-4 ∷ CS24⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS24⁻ ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd24 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-23-4 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 1 (CS14⁻ ∷ []) (refl) ▸
       at 4 2 (CS24⁻ ∷ CS14⁻ ∷ []) (wl0597 (lit c4)) ▸
       at 5 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 2 1 (CS14 ∷ []) (refl) ▸
       at 1 4 (CS24⁻ ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ []) (sym (wl0598 (lit c4))) ▸
       at 3 1 (Sb0-1-4-3 ∷ []) (refl) ▸
       at 0 2 (CS24⁻ ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd24 c4) ▸ done

  b1 : Chain (CS24⁻ ∷ Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (CS24⁻ ∷ Sb0-1-23-4 ∷ [])
  b1 = at 1 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- auto SBOX(0;1;23;4) | CSd24 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd24-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ CS34⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS34⁻ ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd24-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0016 (lit c4))) ▸
       at 1 2 (CS24⁻ ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd24 c4) ▸
       at 0 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0012 (lit c4))) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | SBOXd(1;3;4;0): 5 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·3·4·0⟩ : Ws → ⟪ (Sb0-1-23-4 ∷ Sb⁻1-3-4-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-3-4-0 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·3·4·0⟩ c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ Sb⁻1-3-4-0 ∷ []) (Sb⁻1-3-4-0 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 1 1 (CS34⁻ ∷ []) (refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS34⁻ ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd24-at2332 c4) ▸
       at 1 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 1 (Sb⁻1-3-4-0 ∷ []) (refl) ▸ done


-- auto SBOX(0;1;23;4) | CCZ134 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ134-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ134-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 (lit c4)) ▸
       at 1 2 (CCZ134 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ134 c4) ▸
       at 0 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 (lit c4)) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | CCZ134 @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ134-at243243 : Ws → ⟪ (Sb0-1-42-3 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ134-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 (CCZ124 ∷ Sw34 ∷ []) (lem-nat-3-CCZ123 (lit c4)) ▸
       at 1 2 (CCZ124 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ134-at2332 c4) ▸
       at 0 2 (CCZ123 ∷ Sw34 ∷ []) (lem-nat-3-CCZ124 (lit c4)) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | CCZ134 @0110243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ134-at0110243243 : Ws → ⟪ (Sb1-0-42-3 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ134-at0110243243 c4 = run b0
  where
  b0 : Chain (Sb1-0-42-3 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sb1-0-42-3 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 2 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0103 (lit c4))) ▸
       at 1 2 (CCZ123 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ134-at243243 c4) ▸
       at 0 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0003 (lit c4))) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | CCZ134 @0210243143: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ134-at0210243143 : Ws → ⟪ (Sb2-0-41-3 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ134-at0210243143 c4 = run b0
  where
  b0 : Chain (Sb2-0-41-3 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sb2-0-41-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ (lit c4)) ▸
       at 2 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 (lit c4)) ▸
       at 1 2 (CCZ023 ∷ Sb1-0-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ134-at0110243243 c4) ▸
       at 0 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 (lit c4)) ▸
       at 1 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | SBOX(1;3;4;0) @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·3·4·0⟩-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ Sb1-2-4-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-4-0 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·3·4·0⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ Sb1-2-4-0 ∷ []) (Sb1-2-4-0 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 (Sb1-3-4-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·2·4·0⟩ (lit c4)) ▸
       at 1 2 (Sb1-3-4-0 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·3·4·0⟩ c4) ▸
       at 0 2 (Sb1-2-4-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·3·4·0⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | SBOX(1;3;4;0) @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·3·4·0⟩-at243243 : Ws → ⟪ (Sb0-1-42-3 ∷ Sb1-2-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-3-0 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·3·4·0⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ Sb1-2-3-0 ∷ []) (Sb1-2-3-0 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 (Sb1-2-4-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·2·3·0⟩ (lit c4)) ▸
       at 1 2 (Sb1-2-4-0 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·3·4·0⟩-at2332 c4) ▸
       at 0 2 (Sb1-2-3-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·2·4·0⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | SBOX(1;3;4;0) @0110243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·3·4·0⟩-at0110243243 : Ws → ⟪ (Sb1-0-42-3 ∷ Sb0-2-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-3-1 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·3·4·0⟩-at0110243243 c4 = run b0
  where
  b0 : Chain (Sb1-0-42-3 ∷ Sb0-2-3-1 ∷ []) (Sb0-2-3-1 ∷ Sb1-0-42-3 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 2 2 (Sb1-2-3-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·2·3·1⟩ (lit c4)) ▸
       at 1 2 (Sb1-2-3-0 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·3·4·0⟩-at243243 c4) ▸
       at 0 2 (Sb0-2-3-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·2·3·0⟩ (lit c4)) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | SBOX(1;3;4;0) @0210243143: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·3·4·0⟩-at0210243143 : Ws → ⟪ (Sb2-0-41-3 ∷ Sb0-1-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-3-2 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·3·4·0⟩-at0210243143 c4 = run b0
  where
  b0 : Chain (Sb2-0-41-3 ∷ Sb0-1-3-2 ∷ []) (Sb0-1-3-2 ∷ Sb2-0-41-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ (lit c4)) ▸
       at 2 2 (Sb0-2-3-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·3·2⟩ (lit c4)) ▸
       at 1 2 (Sb0-2-3-1 ∷ Sb1-0-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·3·4·0⟩-at0110243243 c4) ▸
       at 0 2 (Sb0-1-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·3·1⟩ (lit c4)) ▸
       at 1 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | SBOXd(1;3;4;0) @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·3·4·0⟩-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ Sb⁻1-2-4-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-2-4-0 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·3·4·0⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ Sb⁻1-2-4-0 ∷ []) (Sb⁻1-2-4-0 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 (Sb⁻1-3-4-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·2·4·0⟩ (lit c4)) ▸
       at 1 2 (Sb⁻1-3-4-0 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·3·4·0⟩ c4) ▸
       at 0 2 (Sb⁻1-2-4-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·3·4·0⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | SBOXd(1;3;4;0) @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·3·4·0⟩-at243243 : Ws → ⟪ (Sb0-1-42-3 ∷ Sb⁻1-2-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-2-3-0 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·3·4·0⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ Sb⁻1-2-3-0 ∷ []) (Sb⁻1-2-3-0 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 (Sb⁻1-2-4-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨1·2·3·0⟩ (lit c4)) ▸
       at 1 2 (Sb⁻1-2-4-0 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·3·4·0⟩-at2332 c4) ▸
       at 0 2 (Sb⁻1-2-3-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨1·2·4·0⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | SBOXd(1;3;4;0) @0110243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·3·4·0⟩-at0110243243 : Ws → ⟪ (Sb1-0-42-3 ∷ Sb⁻0-2-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-2-3-1 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·3·4·0⟩-at0110243243 c4 = run b0
  where
  b0 : Chain (Sb1-0-42-3 ∷ Sb⁻0-2-3-1 ∷ []) (Sb⁻0-2-3-1 ∷ Sb1-0-42-3 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 2 2 (Sb⁻1-2-3-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·2·3·1⟩ (lit c4)) ▸
       at 1 2 (Sb⁻1-2-3-0 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·3·4·0⟩-at243243 c4) ▸
       at 0 2 (Sb⁻0-2-3-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·2·3·0⟩ (lit c4)) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | SBOXd(1;3;4;0) @0210243143: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·3·4·0⟩-at0210243143 : Ws → ⟪ (Sb2-0-41-3 ∷ Sb⁻0-1-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-3-2 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·3·4·0⟩-at0210243143 c4 = run b0
  where
  b0 : Chain (Sb2-0-41-3 ∷ Sb⁻0-1-3-2 ∷ []) (Sb⁻0-1-3-2 ∷ Sb2-0-41-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ (lit c4)) ▸
       at 2 2 (Sb⁻0-2-3-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨0·1·3·2⟩ (lit c4)) ▸
       at 1 2 (Sb⁻0-2-3-1 ∷ Sb1-0-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·3·4·0⟩-at0110243243 c4) ▸
       at 0 2 (Sb⁻0-1-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨0·2·3·1⟩ (lit c4)) ▸
       at 1 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


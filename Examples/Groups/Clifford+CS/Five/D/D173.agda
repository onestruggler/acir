{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D173 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0001 ; wl0002 ; wl0007 ; wl0031 ; wl0056 ; wl0062 ; wl0076 ; wl0248 ; wl0249 ; wl0250 ; wl0283 ; wl0433 ; wl0474 ; wl0548 ; wl0560 ; wl0714 ; wl0715 ; wl0716 ; wl0717 ; wl0718 ; wl0719 ; wl0720 ; wl0721 ; wl0722 ; wl0723 ; wl0724 ; wl0725 ; wl0726 ; wl0727 ; wl0728 ; wl0729 ; wl0730 ; wl0731 ; wl0732 ; wp0034 ; wp0059 ; wp0126 ; wp0178 ; wp0340 ; wp0341 ; wp0342 ; wp0343 ; wp0344 ; wp0345 ; wp0346 ; wp0347 ; wp0348 ; wp0349 ; wp0350 ; wp0351 ; wp0352 ; wp0353 ; wp0354 ; wp0355 ; wp0356 ; wp0357 ; wp0358 ; wp0359 ; wp0360 ; wp0361 ; wp0362 ; wp0363 ; wp0364 ; wp0365 ; wp0366 ; wp0367 ; wp0368 ; wp0369)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-CS20-beta-ci)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-beta-T-at0210243143 ; lem-sym23-at021021)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-CS12-beta-at021021 ; lem-F5-CS01 ; lem-sym23-at02102331)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at0210243143 ; lem-beta-T-at0210233441 ; lem-sym23-at0210233441 ; lem-sym23-at02102441 ; lem-sym34-at0210243143 ; lem-sym34-at02102441)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-0-SBOX⟨0·1·42·3⟩ ; lem-nat-0-SBOX⟨1·0·42·3⟩ ; lem-nat-1-SBOX⟨1·0·42·3⟩ ; lem-nat-1-SBOX⟨2·0·41·3⟩ ; lem-nat-3-SBOX⟨0·1·32·4⟩ ; lem-nat-3-SBOX⟨0·1·42·3⟩)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-3-SBOX⟨2·0·31·4⟩)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-3-SBOX⟨2·0·41·3⟩)
-- F4 CS01^0|S0^1: 58 steps
lem-F4-CS01ᵖ0∣S0ᵖ1 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS01ᵖ0∣S0ᵖ1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ [])
  b0 = at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 13 1 (CS03⁻ ∷ []) (refl) ▸
       at 12 4 (CS04 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (sym (wp0340 c4)) ▸
       at 14 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸ done

  b1 : Chain (X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ []) (X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ CCZ123 ∷ X4 ∷ CS04 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ [])
  b1 = at 9 4 (CS04 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (sym (wp0341 c4)) ▸
       at 7 1 (CS03 ∷ []) (refl) ▸
       at 6 4 (CS04 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (sym (wp0342 c4)) ▸
       at 8 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 3 4 (CS04 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (sym (wp0341 c4)) ▸
       at 1 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b2 : Chain (X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ CCZ123 ∷ X4 ∷ CS04 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ []) (X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ CS04 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ [])
  b2 = at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0433 (lit c4)) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 17 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 20 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 21 4 (CS04 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (sym (wp0343 c4)) ▸
       at 18 4 (CS04 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (sym (wp0344 c4)) ▸ done

  b3 : Chain (X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ CS04 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ []) (X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ CS04 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ [])
  b3 = at 15 4 (CS04 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (sym (wp0345 c4)) ▸
       at 12 4 (CS04 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (sym (wp0344 c4)) ▸
       at 9 4 (CS04 ∷ X4 ∷ CS23 ∷ X4 ∷ []) (sym (wp0346 c4)) ▸
       at 12 2 [] (wl0283 (lit c4)) ▸
       at 13 2 [] (wl0283 (lit c4)) ▸
       at 14 2 [] (wl0283 (lit c4)) ▸
       at 15 2 [] (wl0283 (lit c4)) ▸
       at 11 5 (CCZ123 ∷ []) (sym (wl0433 (lit c4))) ▸ done

  b4 : Chain (X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ CS04 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ []) (X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ CS04 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ [])
  b4 = at 6 4 (CS04 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (sym (wp0347 c4)) ▸
       at 4 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0433 (lit c4)) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 4 (CS04 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (sym (wp0343 c4)) ▸
       at 12 4 (CS04 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (sym (wp0344 c4)) ▸ done

  b5 : Chain (X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ CS04 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ []) (X4 ∷ Toff204 ∷ X4 ∷ CS04 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ [])
  b5 = at 9 4 (CS04 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (sym (wp0345 c4)) ▸
       at 6 4 (CS04 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (sym (wp0344 c4)) ▸
       at 3 4 (CS04 ∷ X4 ∷ CS23 ∷ X4 ∷ []) (sym (wp0346 c4)) ▸
       at 6 2 [] (wl0283 (lit c4)) ▸
       at 7 2 [] (wl0283 (lit c4)) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 5 5 (CCZ123 ∷ []) (sym (wl0433 (lit c4))) ▸ done

  b6 : Chain (X4 ∷ Toff204 ∷ X4 ∷ CS04 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ []) (CS04 ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ [])
  b6 = at 0 4 (CS04 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (sym (wp0347 c4)) ▸
       at 3 2 [] (wl0283 (lit c4)) ▸
       at 4 2 [] (wl0283 (lit c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸
       at 2 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 3 2 [] (wl0283 (lit c4)) ▸
       at 4 2 [] (wl0283 (lit c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸ done

  b7 : Chain (CS04 ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ []) (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b7 = at 6 2 [] (wl0283 (lit c4)) ▸
       at 2 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done


-- F4 CS01^0|S1^1: 30 steps
lem-F4-CS01ᵖ0∣S1ᵖ1 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS01ᵖ0∣S1ᵖ1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) (X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ [])
  b0 = at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 13 1 (CS03⁻ ∷ []) (refl) ▸
       at 12 4 (CS14 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (sym (wp0348 c4)) ▸
       at 14 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸ done

  b1 : Chain (X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ []) (X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ CCZ123 ∷ X4 ∷ CS14 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ [])
  b1 = at 9 4 (CS14 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (sym (wl0714 (lit c4))) ▸
       at 7 1 (CS03 ∷ []) (refl) ▸
       at 6 4 (CS14 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (sym (wp0349 c4)) ▸
       at 8 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 3 4 (CS14 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (sym (wl0714 (lit c4))) ▸
       at 1 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b2 : Chain (X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ CCZ123 ∷ X4 ∷ CS14 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ []) (CS14 ∷ X4 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ [])
  b2 = at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 4 (CS14 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl0715 (lit c4))) ▸
       at 6 4 (CS14 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (sym (wp0350 c4)) ▸
       at 3 4 (CS14 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl0715 (lit c4))) ▸
       at 0 4 (CS14 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (sym (wp0350 c4)) ▸
       at 3 2 [] (wl0283 (lit c4)) ▸
       at 4 2 [] (wl0283 (lit c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸ done

  b3 : Chain (CS14 ∷ X4 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ []) (CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b3 = at 2 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 3 2 [] (wl0283 (lit c4)) ▸
       at 4 2 [] (wl0283 (lit c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸
       at 6 2 [] (wl0283 (lit c4)) ▸
       at 2 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done


-- F4 CS01^0|S2^1: 30 steps
lem-F4-CS01ᵖ0∣S2ᵖ1 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS01ᵖ0∣S2ᵖ1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS24 ∷ []) (X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ [])
  b0 = at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 13 1 (CS03⁻ ∷ []) (refl) ▸
       at 12 4 (CS24 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (sym (wp0351 c4)) ▸
       at 14 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸ done

  b1 : Chain (X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ []) (X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ CCZ123 ∷ X4 ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ [])
  b1 = at 9 4 (CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (sym (wl0716 (lit c4))) ▸
       at 7 1 (CS03 ∷ []) (refl) ▸
       at 6 4 (CS24 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (sym (wp0352 c4)) ▸
       at 8 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 3 4 (CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (sym (wl0716 (lit c4))) ▸
       at 1 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b2 : Chain (X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ CCZ123 ∷ X4 ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ []) (CS24 ∷ X4 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ [])
  b2 = at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 4 (CS24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl0717 (lit c4))) ▸
       at 6 4 (CS24 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (sym (wp0353 c4)) ▸
       at 3 4 (CS24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl0717 (lit c4))) ▸
       at 0 4 (CS24 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (sym (wp0353 c4)) ▸
       at 3 2 [] (wl0283 (lit c4)) ▸
       at 4 2 [] (wl0283 (lit c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸ done

  b3 : Chain (CS24 ∷ X4 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ []) (CS24 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b3 = at 2 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 3 2 [] (wl0283 (lit c4)) ▸
       at 4 2 [] (wl0283 (lit c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸
       at 6 2 [] (wl0283 (lit c4)) ▸
       at 2 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done


-- F4 CS01^0|S3^1: 30 steps
lem-F4-CS01ᵖ0∣S3ᵖ1 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS01ᵖ0∣S3ᵖ1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS34 ∷ []) (X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ [])
  b0 = at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 13 1 (CS03⁻ ∷ []) (refl) ▸
       at 12 4 (CS34 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (sym (wp0354 c4)) ▸
       at 14 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸ done

  b1 : Chain (X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ []) (X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ CCZ123 ∷ X4 ∷ CS34 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ [])
  b1 = at 9 4 (CS34 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (sym (wl0718 (lit c4))) ▸
       at 7 1 (CS03 ∷ []) (refl) ▸
       at 6 4 (CS34 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (sym (wp0355 c4)) ▸
       at 8 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 3 4 (CS34 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (sym (wl0718 (lit c4))) ▸
       at 1 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b2 : Chain (X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ CCZ123 ∷ X4 ∷ CS34 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ []) (CS34 ∷ X4 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ [])
  b2 = at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 4 (CS34 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl0719 (lit c4))) ▸
       at 6 4 (CS34 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (sym (wp0356 c4)) ▸
       at 3 4 (CS34 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl0719 (lit c4))) ▸
       at 0 4 (CS34 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (sym (wp0356 c4)) ▸
       at 3 2 [] (wl0283 (lit c4)) ▸
       at 4 2 [] (wl0283 (lit c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸ done

  b3 : Chain (CS34 ∷ X4 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ []) (CS34 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b3 = at 2 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 3 2 [] (wl0283 (lit c4)) ▸
       at 4 2 [] (wl0283 (lit c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸
       at 6 2 [] (wl0283 (lit c4)) ▸
       at 2 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done


-- F4 CS01^0|K0^1: 219 steps
lem-F4-CS01ᵖ0∣K0ᵖ1 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS01ᵖ0∣K0ᵖ1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (run b27)))))))))))))))))))))))))))
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ []) (ι ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ [])
  b0 = at 3 1 (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ []) (wp0126 c4) ▸
       at 2 2 (ι ∷ X4 ∷ []) (zc) ▸
       at 1 2 (ι ∷ Sb2-0-41-3 ∷ []) (zc) ▸
       at 0 2 (ι ∷ X4 ∷ []) (zc) ▸
       at 2 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b1 : Chain (ι ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ []) (ι ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ S4⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ [])
  b1 = at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 1 (CS03⁻ ∷ []) (refl) ▸
       at 13 4 (S4⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (sym (wp0357 c4)) ▸
       at 15 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 10 4 (S4⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (sym (wl0720 (lit c4))) ▸
       at 8 1 (CS03 ∷ []) (refl) ▸
       at 7 4 (S4⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) (sym (wp0358 c4)) ▸
       at 9 1 (Sb2-0-3-1 ∷ []) (refl) ▸ done

  b2 : Chain (ι ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ S4⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ []) (ι ∷ X4 ∷ Toff204 ∷ X4 ∷ S4⁻ ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ [])
  b2 = at 4 4 (S4⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (sym (wl0720 (lit c4))) ▸
       at 2 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 3 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 4 (S4⁻ ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl0721 (lit c4))) ▸
       at 7 4 (S4⁻ ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (sym (wp0359 c4)) ▸
       at 4 4 (S4⁻ ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl0721 (lit c4))) ▸ done

  b3 : Chain (ι ∷ X4 ∷ Toff204 ∷ X4 ∷ S4⁻ ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ [])
  b3 = at 1 4 (S4⁻ ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (sym (wp0359 c4)) ▸
       at 4 2 [] (wl0283 (lit c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸
       at 6 2 [] (wl0283 (lit c4)) ▸
       at 3 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 4 2 [] (wl0283 (lit c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸
       at 6 2 [] (wl0283 (lit c4)) ▸ done

  b4 : Chain (ι ∷ S4⁻ ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ [])
  b4 = at 7 2 [] (wl0283 (lit c4)) ▸
       at 3 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 1 (CS03⁻ ∷ []) (refl) ▸ done

  b5 : Chain (ι ∷ S4⁻ ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X4 ∷ CS04 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ [])
  b5 = at 14 4 (CS04 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (sym (wp0340 c4)) ▸
       at 16 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 11 4 (CS04 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (sym (wp0341 c4)) ▸
       at 9 1 (CS03 ∷ []) (refl) ▸
       at 8 4 (CS04 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (sym (wp0342 c4)) ▸
       at 10 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 5 4 (CS04 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (sym (wp0341 c4)) ▸
       at 3 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸ done

  b6 : Chain (ι ∷ S4⁻ ∷ X4 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X4 ∷ CS04 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS12 ∷ X4 ∷ CS04 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ [])
  b6 = at 4 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 12 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0433 (lit c4)) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 16 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 19 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 22 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b7 : Chain (ι ∷ S4⁻ ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS12 ∷ X4 ∷ CS04 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ CS04 ∷ X4 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ X4 ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ [])
  b7 = at 23 4 (CS04 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (sym (wp0343 c4)) ▸
       at 20 4 (CS04 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (sym (wp0344 c4)) ▸
       at 17 4 (CS04 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (sym (wp0345 c4)) ▸
       at 14 4 (CS04 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (sym (wp0344 c4)) ▸
       at 11 4 (CS04 ∷ X4 ∷ CS23 ∷ X4 ∷ []) (sym (wp0346 c4)) ▸
       at 14 2 [] (wl0283 (lit c4)) ▸
       at 15 2 [] (wl0283 (lit c4)) ▸
       at 16 2 [] (wl0283 (lit c4)) ▸ done

  b8 : Chain (ι ∷ S4⁻ ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ CS04 ∷ X4 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ X4 ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS12 ∷ X4 ∷ CS04 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ [])
  b8 = at 17 2 [] (wl0283 (lit c4)) ▸
       at 13 5 (CCZ123 ∷ []) (sym (wl0433 (lit c4))) ▸
       at 8 4 (CS04 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (sym (wp0347 c4)) ▸
       at 6 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0433 (lit c4)) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 16 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b9 : Chain (ι ∷ S4⁻ ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS12 ∷ X4 ∷ CS04 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ Toff204 ∷ X4 ∷ CS04 ∷ X4 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ X4 ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ [])
  b9 = at 17 4 (CS04 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (sym (wp0343 c4)) ▸
       at 14 4 (CS04 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (sym (wp0344 c4)) ▸
       at 11 4 (CS04 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (sym (wp0345 c4)) ▸
       at 8 4 (CS04 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (sym (wp0344 c4)) ▸
       at 5 4 (CS04 ∷ X4 ∷ CS23 ∷ X4 ∷ []) (sym (wp0346 c4)) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸ done

  b10 : Chain (ι ∷ S4⁻ ∷ X4 ∷ Toff204 ∷ X4 ∷ CS04 ∷ X4 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ X4 ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ []) (ι ∷ S4⁻ ∷ CS04 ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ [])
  b10 = at 11 2 [] (wl0283 (lit c4)) ▸
       at 7 5 (CCZ123 ∷ []) (sym (wl0433 (lit c4))) ▸
       at 2 4 (CS04 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (sym (wp0347 c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸
       at 6 2 [] (wl0283 (lit c4)) ▸
       at 7 2 [] (wl0283 (lit c4)) ▸
       at 4 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸ done

  b11 : Chain (ι ∷ S4⁻ ∷ CS04 ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ []) (ι ∷ S4⁻ ∷ CS04 ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ [])
  b11 = at 6 2 [] (wl0283 (lit c4)) ▸
       at 7 2 [] (wl0283 (lit c4)) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸
       at 4 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 4 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b12 : Chain (ι ∷ S4⁻ ∷ CS04 ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ []) (ι ∷ S4⁻ ∷ CS04 ∷ X4 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X4 ∷ K0 ∷ CS04 ∷ K0 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CS04 ∷ [])
  b12 = at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 1 (CS03 ∷ []) (refl) ▸
       at 16 1 (CS03⁻ ∷ []) (refl) ▸
       at 9 12 (K0 ∷ CS04 ∷ K0 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (sym (wp0360 c4)) ▸
       at 13 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 19 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 6 6 (K0 ∷ CS04 ∷ K0 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (sym (wp0361 c4)) ▸
       at 4 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸ done

  b13 : Chain (ι ∷ S4⁻ ∷ CS04 ∷ X4 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X4 ∷ K0 ∷ CS04 ∷ K0 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CS04 ∷ []) (ι ∷ S4⁻ ∷ CS04 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ X4 ∷ CS04 ∷ K0 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CS04 ∷ [])
  b13 = at 5 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 13 2 (K0 ∷ CCZ123 ∷ []) (sym (c₁ (K) (CCZ))) ▸
       at 12 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 14 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0433 (lit c4)) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b14 : Chain (ι ∷ S4⁻ ∷ CS04 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ X4 ∷ CS04 ∷ K0 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CS04 ∷ []) (ι ∷ S4⁻ ∷ CS04 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ CS04 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS12 ∷ X4 ∷ K0 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CS04 ∷ [])
  b14 = at 18 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 21 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 24 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 25 4 (CS04 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (sym (wp0343 c4)) ▸
       at 22 4 (CS04 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (sym (wp0344 c4)) ▸
       at 19 4 (CS04 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (sym (wp0345 c4)) ▸
       at 16 4 (CS04 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (sym (wp0344 c4)) ▸
       at 13 4 (CS04 ∷ X4 ∷ CS23 ∷ X4 ∷ []) (sym (wp0346 c4)) ▸ done

  b15 : Chain (ι ∷ S4⁻ ∷ CS04 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ CS04 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS12 ∷ X4 ∷ K0 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CS04 ∷ []) (ι ∷ S4⁻ ∷ CS04 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ CS04 ∷ K0 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CS04 ∷ [])
  b15 = at 16 2 [] (wl0283 (lit c4)) ▸
       at 17 2 [] (wl0283 (lit c4)) ▸
       at 18 2 [] (wl0283 (lit c4)) ▸
       at 19 2 [] (wl0283 (lit c4)) ▸
       at 15 5 (CCZ123 ∷ []) (sym (wl0433 (lit c4))) ▸
       at 16 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 15 2 (K0 ∷ CCZ123 ∷ []) (sym (c₁ (K) (CCZ))) ▸
       at 14 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸ done

  b16 : Chain (ι ∷ S4⁻ ∷ CS04 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ CS04 ∷ K0 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CS04 ∷ []) (ι ∷ S4⁻ ∷ CS04 ∷ X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ CS12 ∷ X4 ∷ CS04 ∷ K0 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CS04 ∷ [])
  b16 = at 9 6 (K0 ∷ CS04 ∷ K0 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (sym (wp0362 c4)) ▸
       at 8 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 7 2 (K0 ∷ CCZ123 ∷ []) (sym (c₁ (K) (CCZ))) ▸
       at 6 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 8 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0433 (lit c4)) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b17 : Chain (ι ∷ S4⁻ ∷ CS04 ∷ X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ CS12 ∷ X4 ∷ CS04 ∷ K0 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CS04 ∷ []) (ι ∷ S4⁻ ∷ CS04 ∷ X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ CS04 ∷ X4 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS12 ∷ X4 ∷ K0 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CS04 ∷ [])
  b17 = at 18 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 19 4 (CS04 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (sym (wp0343 c4)) ▸
       at 16 4 (CS04 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (sym (wp0344 c4)) ▸
       at 13 4 (CS04 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (sym (wp0345 c4)) ▸
       at 10 4 (CS04 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (sym (wp0344 c4)) ▸
       at 7 4 (CS04 ∷ X4 ∷ CS23 ∷ X4 ∷ []) (sym (wp0346 c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸
       at 11 2 [] (wl0283 (lit c4)) ▸ done

  b18 : Chain (ι ∷ S4⁻ ∷ CS04 ∷ X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ CS04 ∷ X4 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS12 ∷ X4 ∷ K0 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CS04 ∷ []) (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ X4 ∷ Toff204 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CS04 ∷ [])
  b18 = at 12 2 [] (wl0283 (lit c4)) ▸
       at 13 2 [] (wl0283 (lit c4)) ▸
       at 9 5 (CCZ123 ∷ []) (sym (wl0433 (lit c4))) ▸
       at 10 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 9 2 (K0 ∷ CCZ123 ∷ []) (sym (c₁ (K) (CCZ))) ▸
       at 8 2 (K0 ∷ X4 ∷ []) (sym (c₁ (K) (X ↑ ↑ ↑))) ▸
       at 3 6 (K0 ∷ CS04 ∷ K0 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (sym (wp0362 c4)) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸ done

  b19 : Chain (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ X4 ∷ Toff204 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CS04 ∷ []) (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ [])
  b19 = at 9 2 [] (wl0283 (lit c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸
       at 7 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸
       at 11 2 [] (wl0283 (lit c4)) ▸
       at 7 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done

  b20 : Chain (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ [])
  b20 = at 7 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 17 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 19 1 (CS03⁻ ∷ []) (refl) ▸
       at 18 4 (CS04 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (sym (wp0340 c4)) ▸
       at 20 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸ done

  b21 : Chain (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ []) (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ CCZ123 ∷ X4 ∷ CS04 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ [])
  b21 = at 15 4 (CS04 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (sym (wp0341 c4)) ▸
       at 13 1 (CS03 ∷ []) (refl) ▸
       at 12 4 (CS04 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (sym (wp0342 c4)) ▸
       at 14 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 9 4 (CS04 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (sym (wp0341 c4)) ▸
       at 7 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b22 : Chain (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ CCZ123 ∷ X4 ∷ CS04 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ []) (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ CS04 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ [])
  b22 = at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 16 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0433 (lit c4)) ▸
       at 17 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 20 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 23 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 26 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 27 4 (CS04 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (sym (wp0343 c4)) ▸
       at 24 4 (CS04 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (sym (wp0344 c4)) ▸ done

  b23 : Chain (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ CS04 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ []) (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ CS04 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ [])
  b23 = at 21 4 (CS04 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (sym (wp0345 c4)) ▸
       at 18 4 (CS04 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (sym (wp0344 c4)) ▸
       at 15 4 (CS04 ∷ X4 ∷ CS23 ∷ X4 ∷ []) (sym (wp0346 c4)) ▸
       at 18 2 [] (wl0283 (lit c4)) ▸
       at 19 2 [] (wl0283 (lit c4)) ▸
       at 20 2 [] (wl0283 (lit c4)) ▸
       at 21 2 [] (wl0283 (lit c4)) ▸
       at 17 5 (CCZ123 ∷ []) (sym (wl0433 (lit c4))) ▸ done

  b24 : Chain (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ CS04 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ []) (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ CS04 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ [])
  b24 = at 12 4 (CS04 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (sym (wp0347 c4)) ▸
       at 10 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0433 (lit c4)) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 17 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 20 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 21 4 (CS04 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (sym (wp0343 c4)) ▸
       at 18 4 (CS04 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (sym (wp0344 c4)) ▸ done

  b25 : Chain (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ CS04 ∷ X4 ∷ CX13 ∷ X4 ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ []) (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ X4 ∷ Toff204 ∷ X4 ∷ CS04 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ [])
  b25 = at 15 4 (CS04 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (sym (wp0345 c4)) ▸
       at 12 4 (CS04 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (sym (wp0344 c4)) ▸
       at 9 4 (CS04 ∷ X4 ∷ CS23 ∷ X4 ∷ []) (sym (wp0346 c4)) ▸
       at 12 2 [] (wl0283 (lit c4)) ▸
       at 13 2 [] (wl0283 (lit c4)) ▸
       at 14 2 [] (wl0283 (lit c4)) ▸
       at 15 2 [] (wl0283 (lit c4)) ▸
       at 11 5 (CCZ123 ∷ []) (sym (wl0433 (lit c4))) ▸ done

  b26 : Chain (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ X4 ∷ Toff204 ∷ X4 ∷ CS04 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ []) (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ [])
  b26 = at 6 4 (CS04 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (sym (wp0347 c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸
       at 11 2 [] (wl0283 (lit c4)) ▸
       at 8 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸
       at 11 2 [] (wl0283 (lit c4)) ▸ done

  b27 : Chain (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ []) (CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b27 = at 12 2 [] (wl0283 (lit c4)) ▸
       at 8 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 0 7 (CK40 ∷ []) (sym (wp0126 c4)) ▸ done


-- F4 CS01^0|K1^1: 187 steps
lem-F4-CS01ᵖ0∣K1ᵖ1 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS01ᵖ0∣K1ᵖ1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (run b23)))))))))))))))))))))))
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ []) (ι ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ [])
  b0 = at 3 1 (ι1 ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ []) (wp0178 c4) ▸
       at 3 1 (ι ∷ []) (uₛ (iI ↑) (iI) Eq.refl) ▸
       at 2 2 (ι ∷ X4 ∷ []) (zc) ▸
       at 1 2 (ι ∷ Sb2-0-41-3 ∷ []) (zc) ▸
       at 0 2 (ι ∷ X4 ∷ []) (zc) ▸
       at 2 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b1 : Chain (ι ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ []) (ι ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ S4⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ [])
  b1 = at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 1 (CS03⁻ ∷ []) (refl) ▸
       at 13 4 (S4⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (sym (wp0357 c4)) ▸
       at 15 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 10 4 (S4⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (sym (wl0720 (lit c4))) ▸
       at 8 1 (CS03 ∷ []) (refl) ▸
       at 7 4 (S4⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) (sym (wp0358 c4)) ▸ done

  b2 : Chain (ι ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ S4⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ []) (ι ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ S4⁻ ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ [])
  b2 = at 9 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 4 4 (S4⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (sym (wl0720 (lit c4))) ▸
       at 2 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 3 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 4 (S4⁻ ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl0721 (lit c4))) ▸
       at 7 4 (S4⁻ ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (sym (wp0359 c4)) ▸ done

  b3 : Chain (ι ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ S4⁻ ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ [])
  b3 = at 4 4 (S4⁻ ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl0721 (lit c4))) ▸
       at 1 4 (S4⁻ ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (sym (wp0359 c4)) ▸
       at 4 2 [] (wl0283 (lit c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸
       at 6 2 [] (wl0283 (lit c4)) ▸
       at 3 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 4 2 [] (wl0283 (lit c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸ done

  b4 : Chain (ι ∷ S4⁻ ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ [])
  b4 = at 6 2 [] (wl0283 (lit c4)) ▸
       at 7 2 [] (wl0283 (lit c4)) ▸
       at 3 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b5 : Chain (ι ∷ S4⁻ ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ CS14 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ [])
  b5 = at 15 1 (CS03⁻ ∷ []) (refl) ▸
       at 14 4 (CS14 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (sym (wp0348 c4)) ▸
       at 16 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 11 4 (CS14 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (sym (wl0714 (lit c4))) ▸
       at 9 1 (CS03 ∷ []) (refl) ▸
       at 8 4 (CS14 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (sym (wp0349 c4)) ▸
       at 10 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 5 4 (CS14 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (sym (wl0714 (lit c4))) ▸ done

  b6 : Chain (ι ∷ S4⁻ ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ CS14 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ CS14 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ [])
  b6 = at 3 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 4 (CS14 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl0715 (lit c4))) ▸
       at 8 4 (CS14 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (sym (wp0350 c4)) ▸
       at 5 4 (CS14 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl0715 (lit c4))) ▸
       at 2 4 (CS14 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (sym (wp0350 c4)) ▸ done

  b7 : Chain (ι ∷ S4⁻ ∷ CS14 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ CS14 ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ [])
  b7 = at 5 2 [] (wl0283 (lit c4)) ▸
       at 6 2 [] (wl0283 (lit c4)) ▸
       at 7 2 [] (wl0283 (lit c4)) ▸
       at 4 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸
       at 6 2 [] (wl0283 (lit c4)) ▸
       at 7 2 [] (wl0283 (lit c4)) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸ done

  b8 : Chain (ι ∷ S4⁻ ∷ CS14 ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ CS14 ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ CS14 ∷ [])
  b8 = at 4 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 4 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 16 1 (CS03⁻ ∷ []) (refl) ▸
       at 15 6 (K1 ∷ CS14 ∷ K1 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (sym (wp0363 c4)) ▸ done

  b9 : Chain (ι ∷ S4⁻ ∷ CS14 ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ CS14 ∷ X4 ∷ Bx2-0341 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CS14 ∷ [])
  b9 = at 19 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 12 6 (K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (sym (wl0722 (lit c4))) ▸
       at 10 1 (CS03 ∷ []) (refl) ▸
       at 9 6 (K1 ∷ CS14 ∷ K1 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (sym (wp0364 c4)) ▸
       at 13 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 6 6 (K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (sym (wl0722 (lit c4))) ▸
       at 4 1 (Bx2-0431 ∷ []) (lem-sym34-at0210243143 c4) ▸
       at 4 1 (Bx2-0341 ∷ []) (lem-sym23-at02102441 c4) ▸ done

  b10 : Chain (ι ∷ S4⁻ ∷ CS14 ∷ X4 ∷ Bx2-0341 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ CS14 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ X4 ∷ Toff203 ∷ X4 ∷ CS14 ∷ K1 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CS14 ∷ [])
  b10 = at 4 1 (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-beta-T-at0210233441 c4) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 12 6 (K1 ∷ CS14 ∷ K1 ∷ X4 ∷ CCZ124 ∷ X4 ∷ []) (sym (wl0723 (lit c4))) ▸
       at 11 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 10 2 (K1 ∷ Toff203 ∷ []) (sym (wl0724 (lit c4))) ▸
       at 9 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸ done

  b11 : Chain (ι ∷ S4⁻ ∷ CS14 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ X4 ∷ Toff203 ∷ X4 ∷ CS14 ∷ K1 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ CS14 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX03 ∷ CS02 ∷ X4 ∷ CS14 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CS14 ∷ [])
  b11 = at 11 1 (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (sym (wl0548 (lit c4))) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 16 4 (CS14 ∷ X4 ∷ K2⁻ ∷ X4 ∷ []) (sym (wl0725 (lit c4))) ▸
       at 14 1 (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) (wl0560 (lit c4)) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 21 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b12 : Chain (ι ∷ S4⁻ ∷ CS14 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX03 ∷ CS02 ∷ X4 ∷ CS14 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ CS14 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ CS14 ∷ X4 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CS14 ∷ [])
  b12 = at 24 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 25 4 (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (sym (wp0365 c4)) ▸
       at 22 4 (CS14 ∷ X4 ∷ CX03 ∷ X4 ∷ []) (sym (wp0366 c4)) ▸
       at 19 4 (CS14 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (sym (wl0726 (lit c4))) ▸
       at 16 4 (CS14 ∷ X4 ∷ CX03 ∷ X4 ∷ []) (sym (wp0366 c4)) ▸
       at 13 4 (CS14 ∷ X4 ∷ CS23 ∷ X4 ∷ []) (sym (wl0727 (lit c4))) ▸
       at 16 2 [] (wl0283 (lit c4)) ▸
       at 17 2 [] (wl0283 (lit c4)) ▸ done

  b13 : Chain (ι ∷ S4⁻ ∷ CS14 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ CS14 ∷ X4 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ CS14 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CS14 ∷ X4 ∷ Toff203 ∷ K1 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CS14 ∷ [])
  b13 = at 18 2 [] (wl0283 (lit c4)) ▸
       at 19 2 [] (wl0283 (lit c4)) ▸
       at 15 5 (CCZ023 ∷ []) (sym (wl0560 (lit c4))) ▸
       at 10 4 (CS14 ∷ X4 ∷ K2 ∷ X4 ∷ []) (sym (wl0728 (lit c4))) ▸
       at 13 2 [] (wl0283 (lit c4)) ▸
       at 14 2 [] (wl0283 (lit c4)) ▸
       at 12 3 (Toff203 ∷ []) (wl0548 (lit c4)) ▸
       at 13 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸ done

  b14 : Chain (ι ∷ S4⁻ ∷ CS14 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CS14 ∷ X4 ∷ Toff203 ∷ K1 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CCZ023 ∷ K2⁻ ∷ X4 ∷ CS14 ∷ K1 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CS14 ∷ [])
  b14 = at 12 2 (K1 ∷ Toff203 ∷ []) (sym (wl0724 (lit c4))) ▸
       at 11 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 6 6 (K1 ∷ CS14 ∷ K1 ∷ X4 ∷ CCZ124 ∷ X4 ∷ []) (sym (wl0723 (lit c4))) ▸
       at 5 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 4 2 (K1 ∷ Toff203 ∷ []) (sym (wl0724 (lit c4))) ▸
       at 3 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 5 1 (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (sym (wl0548 (lit c4))) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b15 : Chain (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CCZ023 ∷ K2⁻ ∷ X4 ∷ CS14 ∷ K1 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CS14 ∷ [])
  b15 = at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 4 (CS14 ∷ X4 ∷ K2⁻ ∷ X4 ∷ []) (sym (wl0725 (lit c4))) ▸
       at 8 1 (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) (wl0560 (lit c4)) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 18 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 19 4 (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (sym (wp0365 c4)) ▸ done

  b16 : Chain (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ X4 ∷ CS23 ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ X4 ∷ CX03 ∷ X4 ∷ CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ CS14 ∷ X4 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CS14 ∷ [])
  b16 = at 16 4 (CS14 ∷ X4 ∷ CX03 ∷ X4 ∷ []) (sym (wp0366 c4)) ▸
       at 13 4 (CS14 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (sym (wl0726 (lit c4))) ▸
       at 10 4 (CS14 ∷ X4 ∷ CX03 ∷ X4 ∷ []) (sym (wp0366 c4)) ▸
       at 7 4 (CS14 ∷ X4 ∷ CS23 ∷ X4 ∷ []) (sym (wl0727 (lit c4))) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸
       at 11 2 [] (wl0283 (lit c4)) ▸
       at 12 2 [] (wl0283 (lit c4)) ▸
       at 13 2 [] (wl0283 (lit c4)) ▸ done

  b17 : Chain (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ X4 ∷ K2 ∷ X4 ∷ CS14 ∷ X4 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ X4 ∷ X4 ∷ K2⁻ ∷ X4 ∷ K1 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CS14 ∷ [])
  b17 = at 9 5 (CCZ023 ∷ []) (sym (wl0560 (lit c4))) ▸
       at 4 4 (CS14 ∷ X4 ∷ K2 ∷ X4 ∷ []) (sym (wl0728 (lit c4))) ▸
       at 7 2 [] (wl0283 (lit c4)) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸
       at 6 3 (Toff203 ∷ []) (wl0548 (lit c4)) ▸
       at 7 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸
       at 6 2 (K1 ∷ Toff203 ∷ []) (sym (wl0724 (lit c4))) ▸
       at 5 2 (K1 ∷ X4 ∷ []) (sym (c₂ (K ↑) (X ↑ ↑))) ▸ done

  b18 : Chain (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff203 ∷ X4 ∷ X4 ∷ CCZ124 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CS14 ∷ [])
  b18 = at 8 2 [] (wl0283 (lit c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸
       at 7 4 (Bx2-0341 ∷ []) (sym (lem-beta-T-at0210233441 c4)) ▸
       at 7 1 (Bx2-0431 ∷ []) (lem-sym23-at0210233441 c4) ▸
       at 7 1 (Bx2-0413 ∷ []) (lem-sym34-at02102441 c4) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸ done

  b19 : Chain (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CS14 ∷ [])
  b19 = at 10 2 [] (wl0283 (lit c4)) ▸
       at 11 2 [] (wl0283 (lit c4)) ▸
       at 7 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 7 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 17 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b20 : Chain (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CS14 ∷ []) (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ CS14 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ [])
  b20 = at 19 1 (CS03⁻ ∷ []) (refl) ▸
       at 18 4 (CS14 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (sym (wp0348 c4)) ▸
       at 20 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 15 4 (CS14 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (sym (wl0714 (lit c4))) ▸
       at 13 1 (CS03 ∷ []) (refl) ▸
       at 12 4 (CS14 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (sym (wp0349 c4)) ▸
       at 14 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 9 4 (CS14 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (sym (wl0714 (lit c4))) ▸ done

  b21 : Chain (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ CS14 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ []) (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ [])
  b21 = at 7 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 4 (CS14 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl0715 (lit c4))) ▸
       at 12 4 (CS14 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (sym (wp0350 c4)) ▸
       at 9 4 (CS14 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl0715 (lit c4))) ▸
       at 6 4 (CS14 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (sym (wp0350 c4)) ▸ done

  b22 : Chain (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ []) (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ [])
  b22 = at 9 2 [] (wl0283 (lit c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸
       at 11 2 [] (wl0283 (lit c4)) ▸
       at 8 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸
       at 11 2 [] (wl0283 (lit c4)) ▸
       at 12 2 [] (wl0283 (lit c4)) ▸ done

  b23 : Chain (ι ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ []) (CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b23 = at 8 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 0 1 (ι1 ∷ []) (uₛ (iI) (iI ↑) Eq.refl) ▸
       at 0 7 (CK41 ∷ []) (sym (wp0178 c4)) ▸ done


-- auto SBOX(0;1;23;4) | K0 @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at243243 : Ws → ⟪ (Sb0-1-42-3 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ K0 ∷ []) (K0 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 1 2 (K0 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at2332 c4) ▸
       at 0 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | K0 @0110243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at0110243243 : Ws → ⟪ (Sb1-0-42-3 ∷ K1 ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at0110243243 c4 = run b0
  where
  b0 : Chain (Sb1-0-42-3 ∷ K1 ∷ []) (K1 ∷ Sb1-0-42-3 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 2 2 (K0 ∷ Sw01 ∷ []) (sym (wl0031 (lit c4))) ▸
       at 1 2 (K0 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at243243 c4) ▸
       at 0 2 (K1 ∷ Sw01 ∷ []) (sym (wl0076 (lit c4))) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | K0 @0210243143: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at0210243143 : Ws → ⟪ (Sb2-0-41-3 ∷ K2 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at0210243143 c4 = run b0
  where
  b0 : Chain (Sb2-0-41-3 ∷ K2 ∷ []) (K2 ∷ Sb2-0-41-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ (lit c4)) ▸
       at 2 2 (K1 ∷ Sw12 ∷ []) (sym (wl0062 (lit c4))) ▸
       at 1 2 (K1 ∷ Sb1-0-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at0110243243 c4) ▸
       at 0 2 (K2 ∷ Sw12 ∷ []) (sym (wl0056 (lit c4))) ▸
       at 1 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- F4 CS01^0|K2^1: 131 steps
lem-F4-CS01ᵖ0∣K2ᵖ1 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS01ᵖ0∣K2ᵖ1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (run b16))))))))))))))))
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK42 ∷ []) (ι ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ [])
  b0 = at 3 1 (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ []) (wl0729 (lit c4)) ▸
       at 2 2 (ι ∷ X4 ∷ []) (zc) ▸
       at 1 2 (ι ∷ Sb2-0-41-3 ∷ []) (zc) ▸
       at 0 2 (ι ∷ X4 ∷ []) (zc) ▸
       at 2 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b1 : Chain (ι ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ []) (ι ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ S4⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ [])
  b1 = at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 1 (CS03⁻ ∷ []) (refl) ▸
       at 13 4 (S4⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (sym (wp0357 c4)) ▸
       at 15 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 10 4 (S4⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (sym (wl0720 (lit c4))) ▸
       at 8 1 (CS03 ∷ []) (refl) ▸
       at 7 4 (S4⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) (sym (wp0358 c4)) ▸
       at 9 1 (Sb2-0-3-1 ∷ []) (refl) ▸ done

  b2 : Chain (ι ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ S4⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ []) (ι ∷ X4 ∷ Toff204 ∷ X4 ∷ S4⁻ ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ [])
  b2 = at 4 4 (S4⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (sym (wl0720 (lit c4))) ▸
       at 2 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 3 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 4 (S4⁻ ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl0721 (lit c4))) ▸
       at 7 4 (S4⁻ ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (sym (wp0359 c4)) ▸
       at 4 4 (S4⁻ ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl0721 (lit c4))) ▸ done

  b3 : Chain (ι ∷ X4 ∷ Toff204 ∷ X4 ∷ S4⁻ ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ [])
  b3 = at 1 4 (S4⁻ ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (sym (wp0359 c4)) ▸
       at 4 2 [] (wl0283 (lit c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸
       at 6 2 [] (wl0283 (lit c4)) ▸
       at 3 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 4 2 [] (wl0283 (lit c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸
       at 6 2 [] (wl0283 (lit c4)) ▸ done

  b4 : Chain (ι ∷ S4⁻ ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ [])
  b4 = at 7 2 [] (wl0283 (lit c4)) ▸
       at 3 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 1 (CS03⁻ ∷ []) (refl) ▸ done

  b5 : Chain (ι ∷ S4⁻ ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X4 ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ [])
  b5 = at 14 4 (CS24 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (sym (wp0351 c4)) ▸
       at 16 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 11 4 (CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (sym (wl0716 (lit c4))) ▸
       at 9 1 (CS03 ∷ []) (refl) ▸
       at 8 4 (CS24 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (sym (wp0352 c4)) ▸
       at 10 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 5 4 (CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (sym (wl0716 (lit c4))) ▸
       at 3 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸ done

  b6 : Chain (ι ∷ S4⁻ ∷ X4 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X4 ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ []) (ι ∷ S4⁻ ∷ CS24 ∷ X4 ∷ Toff204 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ [])
  b6 = at 4 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 4 (CS24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl0717 (lit c4))) ▸
       at 8 4 (CS24 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (sym (wp0353 c4)) ▸
       at 5 4 (CS24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl0717 (lit c4))) ▸
       at 2 4 (CS24 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (sym (wp0353 c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸ done

  b7 : Chain (ι ∷ S4⁻ ∷ CS24 ∷ X4 ∷ Toff204 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ []) (ι ∷ S4⁻ ∷ CS24 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ [])
  b7 = at 6 2 [] (wl0283 (lit c4)) ▸
       at 7 2 [] (wl0283 (lit c4)) ▸
       at 4 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸
       at 6 2 [] (wl0283 (lit c4)) ▸
       at 7 2 [] (wl0283 (lit c4)) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸
       at 4 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done

  b8 : Chain (ι ∷ S4⁻ ∷ CS24 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ []) (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CS24 ∷ K2 ∷ CS24 ∷ [])
  b8 = at 5 2 (K2 ∷ X4 ∷ []) (sym (wl0730 (lit c4))) ▸
       at 4 2 (K2 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at0210243143 c4) ▸
       at 3 2 (K2 ∷ X4 ∷ []) (sym (wl0730 (lit c4))) ▸
       at 5 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b9 : Chain (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CS24 ∷ K2 ∷ CS24 ∷ []) (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2 ∷ CS24 ∷ [])
  b9 = at 17 1 (CS03⁻ ∷ []) (refl) ▸
       at 16 4 (CS24 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (sym (wp0351 c4)) ▸
       at 18 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 13 4 (CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (sym (wl0716 (lit c4))) ▸
       at 11 1 (CS03 ∷ []) (refl) ▸
       at 10 4 (CS24 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (sym (wp0352 c4)) ▸
       at 12 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 7 4 (CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (sym (wl0716 (lit c4))) ▸ done

  b10 : Chain (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2 ∷ CS24 ∷ []) (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2 ∷ CS24 ∷ [])
  b10 = at 5 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 13 4 (CS24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl0717 (lit c4))) ▸
       at 10 4 (CS24 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (sym (wp0353 c4)) ▸
       at 7 4 (CS24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl0717 (lit c4))) ▸
       at 4 4 (CS24 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (sym (wp0353 c4)) ▸ done

  b11 : Chain (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2 ∷ CS24 ∷ []) (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2 ∷ CS24 ∷ [])
  b11 = at 7 2 [] (wl0283 (lit c4)) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 6 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 7 2 [] (wl0283 (lit c4)) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸ done

  b12 : Chain (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K2 ∷ CS24 ∷ []) (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CS24 ∷ [])
  b12 = at 6 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 7 2 (K2 ∷ X4 ∷ []) (sym (wl0730 (lit c4))) ▸
       at 6 2 (K2 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at0210243143 c4) ▸
       at 5 2 (K2 ∷ X4 ∷ []) (sym (wl0730 (lit c4))) ▸
       at 7 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b13 : Chain (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CS24 ∷ []) (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ [])
  b13 = at 17 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 19 1 (CS03⁻ ∷ []) (refl) ▸
       at 18 4 (CS24 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (sym (wp0351 c4)) ▸
       at 20 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 15 4 (CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (sym (wl0716 (lit c4))) ▸
       at 13 1 (CS03 ∷ []) (refl) ▸
       at 12 4 (CS24 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (sym (wp0352 c4)) ▸
       at 14 1 (Sb2-0-3-1 ∷ []) (refl) ▸ done

  b14 : Chain (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ []) (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ X4 ∷ Toff204 ∷ X4 ∷ CS24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ [])
  b14 = at 9 4 (CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (sym (wl0716 (lit c4))) ▸
       at 7 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 4 (CS24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl0717 (lit c4))) ▸
       at 12 4 (CS24 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (sym (wp0353 c4)) ▸
       at 9 4 (CS24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl0717 (lit c4))) ▸ done

  b15 : Chain (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ X4 ∷ Toff204 ∷ X4 ∷ CS24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ []) (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ [])
  b15 = at 6 4 (CS24 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (sym (wp0353 c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸
       at 11 2 [] (wl0283 (lit c4)) ▸
       at 8 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸
       at 11 2 [] (wl0283 (lit c4)) ▸ done

  b16 : Chain (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ []) (CK42 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b16 = at 12 2 [] (wl0283 (lit c4)) ▸
       at 8 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 0 7 (CK42 ∷ []) (sym (wl0729 (lit c4))) ▸ done


-- F4 CS01^0|K3^1: 131 steps
lem-F4-CS01ᵖ0∣K3ᵖ1 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS01ᵖ0∣K3ᵖ1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (run b16))))))))))))))))
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK43 ∷ []) (ι ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ [])
  b0 = at 3 1 (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ []) (wl0731 (lit c4)) ▸
       at 2 2 (ι ∷ X4 ∷ []) (zc) ▸
       at 1 2 (ι ∷ Sb2-0-41-3 ∷ []) (zc) ▸
       at 0 2 (ι ∷ X4 ∷ []) (zc) ▸
       at 2 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b1 : Chain (ι ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ []) (ι ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ S4⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ [])
  b1 = at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 1 (CS03⁻ ∷ []) (refl) ▸
       at 13 4 (S4⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (sym (wp0357 c4)) ▸
       at 15 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 10 4 (S4⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (sym (wl0720 (lit c4))) ▸
       at 8 1 (CS03 ∷ []) (refl) ▸
       at 7 4 (S4⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) (sym (wp0358 c4)) ▸
       at 9 1 (Sb2-0-3-1 ∷ []) (refl) ▸ done

  b2 : Chain (ι ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ S4⁻ ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ []) (ι ∷ X4 ∷ Toff204 ∷ X4 ∷ S4⁻ ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ [])
  b2 = at 4 4 (S4⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (sym (wl0720 (lit c4))) ▸
       at 2 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 3 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 4 (S4⁻ ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl0721 (lit c4))) ▸
       at 7 4 (S4⁻ ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (sym (wp0359 c4)) ▸
       at 4 4 (S4⁻ ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl0721 (lit c4))) ▸ done

  b3 : Chain (ι ∷ X4 ∷ Toff204 ∷ X4 ∷ S4⁻ ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ [])
  b3 = at 1 4 (S4⁻ ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (sym (wp0359 c4)) ▸
       at 4 2 [] (wl0283 (lit c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸
       at 6 2 [] (wl0283 (lit c4)) ▸
       at 3 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 4 2 [] (wl0283 (lit c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸
       at 6 2 [] (wl0283 (lit c4)) ▸ done

  b4 : Chain (ι ∷ S4⁻ ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ [])
  b4 = at 7 2 [] (wl0283 (lit c4)) ▸
       at 3 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 13 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 1 (CS03⁻ ∷ []) (refl) ▸ done

  b5 : Chain (ι ∷ S4⁻ ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X4 ∷ CS34 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ [])
  b5 = at 14 4 (CS34 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (sym (wp0354 c4)) ▸
       at 16 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 11 4 (CS34 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (sym (wl0718 (lit c4))) ▸
       at 9 1 (CS03 ∷ []) (refl) ▸
       at 8 4 (CS34 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (sym (wp0355 c4)) ▸
       at 10 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 5 4 (CS34 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (sym (wl0718 (lit c4))) ▸
       at 3 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸ done

  b6 : Chain (ι ∷ S4⁻ ∷ X4 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X4 ∷ CS34 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ []) (ι ∷ S4⁻ ∷ CS34 ∷ X4 ∷ Toff204 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ [])
  b6 = at 4 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 7 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 10 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 4 (CS34 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl0719 (lit c4))) ▸
       at 8 4 (CS34 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (sym (wp0356 c4)) ▸
       at 5 4 (CS34 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl0719 (lit c4))) ▸
       at 2 4 (CS34 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (sym (wp0356 c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸ done

  b7 : Chain (ι ∷ S4⁻ ∷ CS34 ∷ X4 ∷ Toff204 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ []) (ι ∷ S4⁻ ∷ CS34 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ [])
  b7 = at 6 2 [] (wl0283 (lit c4)) ▸
       at 7 2 [] (wl0283 (lit c4)) ▸
       at 4 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 5 2 [] (wl0283 (lit c4)) ▸
       at 6 2 [] (wl0283 (lit c4)) ▸
       at 7 2 [] (wl0283 (lit c4)) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸
       at 4 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done

  b8 : Chain (ι ∷ S4⁻ ∷ CS34 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ []) (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CS34 ∷ K3 ∷ CS34 ∷ [])
  b8 = at 5 2 (K3 ∷ X4 ∷ []) (sym (wl0732 (lit c4))) ▸
       at 4 2 (K3 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at0210243143 c4) ▸
       at 3 2 (K3 ∷ X4 ∷ []) (sym (wl0732 (lit c4))) ▸
       at 5 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b9 : Chain (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CS34 ∷ K3 ∷ CS34 ∷ []) (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ CS34 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K3 ∷ CS34 ∷ [])
  b9 = at 17 1 (CS03⁻ ∷ []) (refl) ▸
       at 16 4 (CS34 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (sym (wp0354 c4)) ▸
       at 18 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 13 4 (CS34 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (sym (wl0718 (lit c4))) ▸
       at 11 1 (CS03 ∷ []) (refl) ▸
       at 10 4 (CS34 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (sym (wp0355 c4)) ▸
       at 12 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 7 4 (CS34 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (sym (wl0718 (lit c4))) ▸ done

  b10 : Chain (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ CS34 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K3 ∷ CS34 ∷ []) (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K3 ∷ CS34 ∷ [])
  b10 = at 5 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 9 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 12 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 13 4 (CS34 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl0719 (lit c4))) ▸
       at 10 4 (CS34 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (sym (wp0356 c4)) ▸
       at 7 4 (CS34 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl0719 (lit c4))) ▸
       at 4 4 (CS34 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (sym (wp0356 c4)) ▸ done

  b11 : Chain (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K3 ∷ CS34 ∷ []) (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K3 ∷ CS34 ∷ [])
  b11 = at 7 2 [] (wl0283 (lit c4)) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 6 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 7 2 [] (wl0283 (lit c4)) ▸
       at 8 2 [] (wl0283 (lit c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸ done

  b12 : Chain (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ K3 ∷ CS34 ∷ []) (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CS34 ∷ [])
  b12 = at 6 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 7 2 (K3 ∷ X4 ∷ []) (sym (wl0732 (lit c4))) ▸
       at 6 2 (K3 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at0210243143 c4) ▸
       at 5 2 (K3 ∷ X4 ∷ []) (sym (wl0732 (lit c4))) ▸
       at 7 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸ done

  b13 : Chain (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CS34 ∷ []) (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ [])
  b13 = at 17 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 19 1 (CS03⁻ ∷ []) (refl) ▸
       at 18 4 (CS34 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (sym (wp0354 c4)) ▸
       at 20 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 15 4 (CS34 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (sym (wl0718 (lit c4))) ▸
       at 13 1 (CS03 ∷ []) (refl) ▸
       at 12 4 (CS34 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (sym (wp0355 c4)) ▸
       at 14 1 (Sb2-0-3-1 ∷ []) (refl) ▸ done

  b14 : Chain (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ []) (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ X4 ∷ Toff204 ∷ X4 ∷ CS34 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ [])
  b14 = at 9 4 (CS34 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (sym (wl0718 (lit c4))) ▸
       at 7 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 14 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 4 (CS34 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl0719 (lit c4))) ▸
       at 12 4 (CS34 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (sym (wp0356 c4)) ▸
       at 9 4 (CS34 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl0719 (lit c4))) ▸ done

  b15 : Chain (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ X4 ∷ Toff204 ∷ X4 ∷ CS34 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ []) (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ [])
  b15 = at 6 4 (CS34 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (sym (wp0356 c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸
       at 11 2 [] (wl0283 (lit c4)) ▸
       at 8 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 9 2 [] (wl0283 (lit c4)) ▸
       at 10 2 [] (wl0283 (lit c4)) ▸
       at 11 2 [] (wl0283 (lit c4)) ▸ done

  b16 : Chain (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ []) (CK43 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b16 = at 12 2 [] (wl0283 (lit c4)) ▸
       at 8 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 0 7 (CK43 ∷ []) (sym (wl0731 (lit c4))) ▸ done


-- auto CS01 | BOX(2;0314): 3 steps
lem-auto-CS01-∣-BOX⟨2·0314⟩ : Ws → ⟪ (CS01 ∷ Bx2-0314 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0314 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·0314⟩ c4 = run b0
  where
  b0 : Chain (CS01 ∷ Bx2-0314 ∷ []) (Bx2-0314 ∷ CS01 ∷ [])
  b0 = at 1 1 (Bx2-0134 ∷ []) (lem-sym23-at02102331 c4) ▸
       at 0 2 (Bx2-0134 ∷ CS01 ∷ []) (lem-CS12-beta-at021021 c4) ▸
       at 0 1 (Bx2-0314 ∷ []) (lem-sym23-at021021 c4) ▸ done


-- auto CS01 | SBOX(2;0;31;4): 11 steps
lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩ : Ws → ⟪ (CS01 ∷ Sb2-0-31-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-31-4 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS01 ∷ Sb2-0-31-4 ∷ []) (Bx2-0314 ∷ Toff413 ∷ Sb2-0-4-1 ∷ Toff413 ∷ CS01 ∷ CS04⁻ ∷ [])
  b0 = at 1 1 (Bx2-0314 ∷ Toff413 ∷ Sb2-0-4-1 ∷ Toff413 ∷ Sb⁻2-0-4-1 ∷ []) (refl) ▸
       at 0 2 (Bx2-0314 ∷ CS01 ∷ []) (lem-auto-CS01-∣-BOX⟨2·0314⟩ c4) ▸
       at 1 2 (Toff413 ∷ CS01 ∷ []) (wp0367 c4) ▸
       at 3 1 (CS04 ∷ []) (refl) ▸
       at 2 2 (CS04 ∷ CS01 ∷ []) (wp0368 c4) ▸
       at 2 1 (Sb2-0-4-1 ∷ []) (refl) ▸
       at 3 2 (Toff413 ∷ CS01 ∷ []) (wp0367 c4) ▸
       at 5 1 (CS04⁻ ∷ []) (refl) ▸ done

  b1 : Chain (Bx2-0314 ∷ Toff413 ∷ Sb2-0-4-1 ∷ Toff413 ∷ CS01 ∷ CS04⁻ ∷ []) (Sb2-0-31-4 ∷ CS01 ∷ [])
  b1 = at 4 2 (CS04⁻ ∷ CS01 ∷ []) (wp0369 c4) ▸
       at 4 1 (Sb⁻2-0-4-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-0-31-4 ∷ []) (refl) ▸ done


-- auto CS01 | SBOX(2;0;31;4) @3443: 7 steps
lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at3443 : Ws → ⟪ (CS01 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at3443 c4 = run b0
  where
  b0 : Chain (CS01 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CS01 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 2 2 (Sb2-0-31-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·0·41·3⟩ (lit c4)) ▸
       at 1 2 (Sb2-0-31-4 ∷ CS01 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩ c4) ▸
       at 0 2 (Sb2-0-41-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·0·31·4⟩ (lit c4)) ▸
       at 1 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- F4 CS01^0|CS01^1: 63 steps
lem-F4-CS01ᵖ0∣CS01ᵖ1 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS01ᵖ0∣CS01ᵖ1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (CS01 ∷ CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ Toff204 ∷ CCZ024 ∷ [])
  b0 = at 0 4 (CS01 ∷ []) (lem-F5-CS01 c4) ▸
       at 1 0 (CCZ024 ∷ CCZ024 ∷ []) (sym (wp0034 c4)) ▸
       at 2 0 (Toff204 ∷ Toff204 ∷ []) (sym (wp0059 c4)) ▸
       at 3 0 (CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ []) (sym (wl0474 (lit c4))) ▸
       at 5 1 (Bx2-03 ∷ []) (refl) ▸
       at 8 1 (Bx2-03 ∷ []) (refl) ▸
       at 3 6 (Bx0-213 ∷ []) (refl) ▸
       at 4 1 (Bx⁻2-03 ∷ []) (refl) ▸ done

  b1 : Chain (CS01 ∷ CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ Toff204 ∷ CCZ024 ∷ []) (CS01 ∷ CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CCZ024 ∷ Toff204 ∷ Bx⁻0-213 ∷ Toff204 ∷ CCZ024 ∷ [])
  b1 = at 7 1 (Bx⁻2-03 ∷ []) (refl) ▸
       at 4 6 (Bx⁻0-213 ∷ []) (refl) ▸
       at 4 0 (Toff204 ∷ Toff204 ∷ []) (sym (wp0059 c4)) ▸
       at 5 0 (CCZ024 ∷ CCZ024 ∷ []) (sym (wp0034 c4)) ▸
       at 6 0 (CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ []) (sym (wl0474 (lit c4))) ▸
       at 8 1 (Bx2-03 ∷ []) (refl) ▸
       at 11 1 (Bx2-03 ∷ []) (refl) ▸
       at 6 6 (Bx0-213 ∷ []) (refl) ▸ done

  b2 : Chain (CS01 ∷ CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CCZ024 ∷ Toff204 ∷ Bx⁻0-213 ∷ Toff204 ∷ CCZ024 ∷ []) (CS01 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ CS03⁻ ∷ Toff314 ∷ Bx⁻2-0413 ∷ [])
  b2 = at 7 1 (Bx⁻2-03 ∷ []) (refl) ▸
       at 10 1 (Bx⁻2-03 ∷ []) (refl) ▸
       at 7 6 (Bx⁻0-213 ∷ []) (refl) ▸
       at 1 6 (Bx2-0413 ∷ []) (refl) ▸
       at 2 6 (Bx⁻2-0413 ∷ []) (refl) ▸
       at 2 0 (Toff314 ∷ Toff314 ∷ []) (sym (wl0248 (lit c4))) ▸
       at 3 0 (CS03 ∷ CS03⁻ ∷ []) (sym (wl0250 (lit c4))) ▸
       at 3 1 (Sb2-0-3-1 ∷ []) (refl) ▸ done

  b3 : Chain (CS01 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ CS03⁻ ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) (Sb2-0-41-3 ∷ CS01 ∷ Sb⁻2-0-41-3 ∷ [])
  b3 = at 4 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 4 0 (Toff314 ∷ Toff314 ∷ []) (sym (wl0248 (lit c4))) ▸
       at 5 0 (CS03⁻ ∷ CS03 ∷ []) (sym (wl0249 (lit c4))) ▸
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
       at 8 2 [] (wl0249 (lit c4)) ▸
       at 7 2 [] (wl0248 (lit c4)) ▸
       at 6 1 (CS03 ∷ []) (refl) ▸ done

  b5 : Chain (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ Bx⁻0-213 ∷ CCZ024 ∷ Toff204 ∷ Bx⁻0-213 ∷ Toff204 ∷ CCZ024 ∷ [])
  b5 = at 7 1 (CS03⁻ ∷ []) (refl) ▸
       at 6 2 [] (wl0250 (lit c4)) ▸
       at 5 2 [] (wl0248 (lit c4)) ▸
       at 5 1 (Bx⁻0-213 ∷ CCZ024 ∷ Toff204 ∷ Bx⁻0-213 ∷ Toff204 ∷ CCZ024 ∷ []) (refl) ▸
       at 4 1 (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ []) (refl) ▸
       at 9 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) (refl) ▸
       at 11 1 (CZ03 ∷ []) (refl) ▸
       at 14 1 (CZ03 ∷ []) (refl) ▸ done

  b6 : Chain (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ Bx⁻0-213 ∷ CCZ024 ∷ Toff204 ∷ Bx⁻0-213 ∷ Toff204 ∷ CCZ024 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CCZ024 ∷ Toff204 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ Bx⁻0-213 ∷ Toff204 ∷ CCZ024 ∷ [])
  b6 = at 15 1 (Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ []) (refl) ▸
       at 15 1 (CZ03 ∷ []) (refl) ▸
       at 18 1 (CZ03 ∷ []) (refl) ▸
       at 9 12 [] (wl0474 (lit c4)) ▸
       at 8 2 [] (wp0034 c4) ▸
       at 7 2 [] (wp0059 c4) ▸
       at 6 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) (refl) ▸
       at 8 1 (CZ03 ∷ []) (refl) ▸ done

  b7 : Chain (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CCZ024 ∷ Toff204 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ Bx⁻0-213 ∷ Toff204 ∷ CCZ024 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b7 = at 11 1 (CZ03 ∷ []) (refl) ▸
       at 12 1 (Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ []) (refl) ▸
       at 12 1 (CZ03 ∷ []) (refl) ▸
       at 15 1 (CZ03 ∷ []) (refl) ▸
       at 6 12 [] (wl0474 (lit c4)) ▸
       at 5 2 [] (wp0059 c4) ▸
       at 4 2 [] (wp0034 c4) ▸ done


-- auto BOX(0;1234) | CSd02: 1 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd02 : Ws → ⟪ (Bx0-1234 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd02 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ Bx0-1234 ∷ [])
  b0 = at 0 2 (CS02⁻ ∷ Bx0-1234 ∷ []) (sym (lem-CS20-beta-ci c4)) ▸ done


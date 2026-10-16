{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D200 where

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
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-beta-inv-at243243 ; lem-sym12-at14213243 ; lem-sym23-at14213243)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-sym12-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at243243 ; lem-auto-BOX⟨0·1234⟩-∣-CS14-at243243 ; lem-auto-BOX⟨0·1234⟩-∣-CSd14-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-X1-beta-at14213243 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at243243 ; lem-auto-BOX⟨0·1234⟩-∣-CS13-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D145 using (lem-T312-beta-at1441 ; lem-sym23-at143143 ; lem-sym34-at143143 ; lem-sym34-at1441)
open import Examples.Groups.Clifford+CS.Five.D.D174 using (lem-auto-CCZ012-∣-SBOX⟨3·0·42·1⟩-at1331 ; lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at12213443)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-0-SBOX⟨0·1·42·3⟩ ; lem-nat-0-SBOX⟨1·0·42·3⟩)
-- F5 CS12: 38 steps
lem-F5-CS12 : Complete 4 → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ []) ⟫ʷ
lem-F5-CS12 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (run b4))))
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (CCZ123 ∷ Bx0-1423 ∷ X4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b0 = at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx0-4123 ∷ []) (lem-sym12-at243243 c4) ▸
       at 0 3 (CCZ123 ∷ Bx0-4123 ∷ []) (lem-X1-beta-at14213243 c4) ▸
       at 1 1 (Bx0-1423 ∷ []) (lem-sym12-at14213243 c4) ▸
       at 8 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ123 ∷ Bx0-1423 ∷ X4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (CCZ123 ∷ CS12 ∷ CCZ123 ∷ CS13 ∷ Toff324 ∷ Toff324 ∷ Bx0-4123 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b1 = at 10 1 (CS13 ∷ []) (refl) ▸
       at 12 1 (CS13⁻ ∷ []) (refl) ▸
       at 2 6 (CS12 ∷ CCZ123 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ []) (lw0 c4 (X4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ []) (CS12 ∷ CCZ123 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS12 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS13-at243243 c4) ▸
       at 2 2 (CCZ123 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at243243 c4) ▸
       at 3 2 (CS13 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14-at243243 c4) ▸
       at 4 0 (Toff324 ∷ Toff324 ∷ []) (lw0 c4 [] (Toff324 ∷ Toff324 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Bx0-4123 ∷ []) (lem-sym12-at243243 c4) ▸ done

  b2 : Chain (CCZ123 ∷ CS12 ∷ CCZ123 ∷ CS13 ∷ Toff324 ∷ Toff324 ∷ Bx0-4123 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (CCZ123 ∷ CS12 ∷ CCZ123 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ Bx0-1423 ∷ Toff324 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b2 = at 6 1 (Bx0-4213 ∷ []) (lem-sym23-at14213243 c4) ▸
       at 6 1 (Bx0-4231 ∷ []) (lem-sym34-at143143 c4) ▸
       at 5 3 (Bx0-4231 ∷ CCZ124 ∷ []) (lem-T312-beta-at1441 c4) ▸
       at 5 1 (Bx0-4213 ∷ []) (lem-sym34-at1441 c4) ▸
       at 5 1 (Bx0-4123 ∷ []) (lem-sym23-at143143 c4) ▸
       at 5 1 (Bx0-1423 ∷ []) (lem-sym12-at14213243 c4) ▸
       at 5 2 (CCZ124 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at243243 c4) ▸
       at 6 2 (CS13⁻ ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14-at243243 c4) ▸ done

  b3 : Chain (CCZ123 ∷ CS12 ∷ CCZ123 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ Bx0-1423 ∷ Toff324 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (CCZ123 ∷ CS12 ∷ CCZ123 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ Bx0-1423 ∷ CCZ124 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b3 = at 7 0 (Toff324 ∷ Toff324 ∷ []) (lw0 c4 [] (Toff324 ∷ Toff324 ∷ []) tt tt Eq.refl) ▸
       at 9 1 (Bx0-4123 ∷ []) (lem-sym12-at243243 c4) ▸
       at 9 1 (Bx0-4213 ∷ []) (lem-sym23-at14213243 c4) ▸
       at 9 1 (Bx0-4231 ∷ []) (lem-sym34-at143143 c4) ▸
       at 8 3 (Bx0-4231 ∷ CCZ124 ∷ []) (lem-T312-beta-at1441 c4) ▸
       at 8 1 (Bx0-4213 ∷ []) (lem-sym34-at1441 c4) ▸
       at 8 1 (Bx0-4123 ∷ []) (lem-sym23-at143143 c4) ▸
       at 8 1 (Bx0-1423 ∷ []) (lem-sym12-at14213243 c4) ▸ done

  b4 : Chain (CCZ123 ∷ CS12 ∷ CCZ123 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ Bx0-1423 ∷ CCZ124 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (CS12 ∷ [])
  b4 = at 8 2 (CCZ124 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at243243 c4) ▸
       at 1 5 (CCZ124 ∷ CS12 ∷ CCZ123 ∷ CS13 ∷ Toff324 ∷ []) (lw0 c4 (CS12 ∷ CCZ123 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ []) (CCZ124 ∷ CS12 ∷ CCZ123 ∷ CS13 ∷ Toff324 ∷ []) tt tt Eq.refl) ▸
       at 2 7 (CCZ124 ∷ CS12 ∷ CCZ123 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ []) (lw0 c4 (CS12 ∷ CCZ123 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ []) (CCZ124 ∷ CS12 ∷ CCZ123 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ []) tt tt Eq.refl) ▸
       at 1 2 [] (lw0 c4 (CCZ124 ∷ CCZ124 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 [] (lem-beta-inv-at243243 c4) ▸
       at 0 11 (CS12 ∷ []) (lw0 c4 (CCZ123 ∷ CS12 ∷ CCZ123 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (CS12 ∷ []) tt tt Eq.refl) ▸ done


-- auto CS01 | SBOX(2;0;31;4) @0112203443: 7 steps
lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at0112203443 : Complete 4 → ⟪ (CS12 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CS12 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at0112203443 c4 = run b0
  where
  b0 : Chain (CS12 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ CS12 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS02 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ c4) ▸
       at 1 2 (Sb1-0-42-3 ∷ CS02 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at12213443 c4) ▸
       at 0 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ c4) ▸
       at 1 2 (CS12 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS02 ∷ []) (CS12 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- F4 CS12^0|CS12^1: 63 steps
lem-F4-CS12ᵖ0∣CS12ᵖ1 : Complete 4 → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS12ᵖ0∣CS12ᵖ1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (CS12 ∷ CCZ014 ∷ Toff014 ∷ Bx1-023 ∷ Bx⁻0-13 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ Toff014 ∷ CCZ014 ∷ [])
  b0 = at 0 4 (CS12 ∷ []) (lem-F5-CS12 c4) ▸
       at 1 0 (CCZ014 ∷ CCZ014 ∷ []) (pw2 c4 [] (CCZ014 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 2 0 (Toff014 ∷ Toff014 ∷ []) (pw2 c4 [] (Toff014 ∷ Toff014 ∷ []) tt tt Eq.refl) ▸
       at 3 0 (CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ CZ13 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ []) (lw4 c4 [] (CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ CZ13 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Bx0-13 ∷ []) (refl) ▸
       at 8 1 (Bx0-13 ∷ []) (refl) ▸
       at 3 6 (Bx1-023 ∷ []) (refl) ▸
       at 4 1 (Bx⁻0-13 ∷ []) (refl) ▸ done

  b1 : Chain (CS12 ∷ CCZ014 ∷ Toff014 ∷ Bx1-023 ∷ Bx⁻0-13 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ Toff014 ∷ CCZ014 ∷ []) (CS12 ∷ CCZ014 ∷ Toff014 ∷ Bx1-023 ∷ Toff014 ∷ CCZ014 ∷ Bx1-023 ∷ CZ13 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CCZ014 ∷ Toff014 ∷ Bx⁻1-023 ∷ Toff014 ∷ CCZ014 ∷ [])
  b1 = at 7 1 (Bx⁻0-13 ∷ []) (refl) ▸
       at 4 6 (Bx⁻1-023 ∷ []) (refl) ▸
       at 4 0 (Toff014 ∷ Toff014 ∷ []) (pw2 c4 [] (Toff014 ∷ Toff014 ∷ []) tt tt Eq.refl) ▸
       at 5 0 (CCZ014 ∷ CCZ014 ∷ []) (pw2 c4 [] (CCZ014 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 6 0 (CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ CZ13 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ []) (lw4 c4 [] (CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ CZ13 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 8 1 (Bx0-13 ∷ []) (refl) ▸
       at 11 1 (Bx0-13 ∷ []) (refl) ▸
       at 6 6 (Bx1-023 ∷ []) (refl) ▸ done

  b2 : Chain (CS12 ∷ CCZ014 ∷ Toff014 ∷ Bx1-023 ∷ Toff014 ∷ CCZ014 ∷ Bx1-023 ∷ CZ13 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CCZ014 ∷ Toff014 ∷ Bx⁻1-023 ∷ Toff014 ∷ CCZ014 ∷ []) (CS12 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ CS13⁻ ∷ Toff324 ∷ Bx⁻0-1423 ∷ [])
  b2 = at 7 1 (Bx⁻0-13 ∷ []) (refl) ▸
       at 10 1 (Bx⁻0-13 ∷ []) (refl) ▸
       at 7 6 (Bx⁻1-023 ∷ []) (refl) ▸
       at 1 6 (Bx0-1423 ∷ []) (refl) ▸
       at 2 6 (Bx⁻0-1423 ∷ []) (refl) ▸
       at 2 0 (Toff324 ∷ Toff324 ∷ []) (lw0 c4 [] (Toff324 ∷ Toff324 ∷ []) tt tt Eq.refl) ▸
       at 3 0 (CS13 ∷ CS13⁻ ∷ []) (lw4 c4 [] (CS13 ∷ CS13⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb0-1-3-2 ∷ []) (refl) ▸ done

  b3 : Chain (CS12 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ CS13⁻ ∷ Toff324 ∷ Bx⁻0-1423 ∷ []) (Sb0-1-42-3 ∷ CS12 ∷ Sb⁻0-1-42-3 ∷ [])
  b3 = at 4 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 4 0 (Toff324 ∷ Toff324 ∷ []) (lw0 c4 [] (Toff324 ∷ Toff324 ∷ []) tt tt Eq.refl) ▸
       at 5 0 (CS13⁻ ∷ CS13 ∷ []) (lw4 c4 [] (CS13⁻ ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 6 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 1 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 2 5 (Sb⁻0-1-42-3 ∷ []) (refl) ▸
       at 0 2 (Sb0-1-42-3 ∷ CS12 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at0112203443 c4) ▸ done

  b4 : Chain (Sb0-1-42-3 ∷ CS12 ∷ Sb⁻0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Sb⁻0-1-3-2 ∷ Toff324 ∷ Bx⁻0-1423 ∷ [])
  b4 = at 1 1 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F5-CS12 c4)) ▸
       at 5 1 (Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ Toff324 ∷ Bx⁻0-1423 ∷ []) (refl) ▸
       at 4 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 8 1 (CS13⁻ ∷ []) (refl) ▸
       at 9 1 (CS13 ∷ []) (refl) ▸
       at 8 2 [] (lw4 c4 (CS13⁻ ∷ CS13 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 [] (lw0 c4 (Toff324 ∷ Toff324 ∷ []) [] tt tt Eq.refl) ▸
       at 6 1 (CS13 ∷ []) (refl) ▸ done

  b5 : Chain (Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Sb⁻0-1-3-2 ∷ Toff324 ∷ Bx⁻0-1423 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CCZ014 ∷ Toff014 ∷ Bx1-023 ∷ Toff014 ∷ CCZ014 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ Bx⁻1-023 ∷ CCZ014 ∷ Toff014 ∷ Bx⁻1-023 ∷ Toff014 ∷ CCZ014 ∷ [])
  b5 = at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 6 2 [] (lw4 c4 (CS13 ∷ CS13⁻ ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 [] (lw0 c4 (Toff324 ∷ Toff324 ∷ []) [] tt tt Eq.refl) ▸
       at 5 1 (Bx⁻1-023 ∷ CCZ014 ∷ Toff014 ∷ Bx⁻1-023 ∷ Toff014 ∷ CCZ014 ∷ []) (refl) ▸
       at 4 1 (CCZ014 ∷ Toff014 ∷ Bx1-023 ∷ Toff014 ∷ CCZ014 ∷ Bx1-023 ∷ []) (refl) ▸
       at 9 1 (CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ []) (refl) ▸
       at 11 1 (CZ13 ∷ []) (refl) ▸
       at 14 1 (CZ13 ∷ []) (refl) ▸ done

  b6 : Chain (Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CCZ014 ∷ Toff014 ∷ Bx1-023 ∷ Toff014 ∷ CCZ014 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ Bx⁻1-023 ∷ CCZ014 ∷ Toff014 ∷ Bx⁻1-023 ∷ Toff014 ∷ CCZ014 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CCZ014 ∷ Toff014 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ Bx⁻1-023 ∷ Toff014 ∷ CCZ014 ∷ [])
  b6 = at 15 1 (Bx⁻0-13 ∷ CCZ012 ∷ Toff102 ∷ Bx⁻0-13 ∷ Toff102 ∷ CCZ012 ∷ []) (refl) ▸
       at 15 1 (CZ13 ∷ []) (refl) ▸
       at 18 1 (CZ13 ∷ []) (refl) ▸
       at 9 12 [] (lw4 c4 (CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ CZ13 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 [] (pw2 c4 (CCZ014 ∷ CCZ014 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 [] (pw2 c4 (Toff014 ∷ Toff014 ∷ []) [] tt tt Eq.refl) ▸
       at 6 1 (CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ []) (refl) ▸
       at 8 1 (CZ13 ∷ []) (refl) ▸ done

  b7 : Chain (Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CCZ014 ∷ Toff014 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ Bx⁻1-023 ∷ Toff014 ∷ CCZ014 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b7 = at 11 1 (CZ13 ∷ []) (refl) ▸
       at 12 1 (Bx⁻0-13 ∷ CCZ012 ∷ Toff102 ∷ Bx⁻0-13 ∷ Toff102 ∷ CCZ012 ∷ []) (refl) ▸
       at 12 1 (CZ13 ∷ []) (refl) ▸
       at 15 1 (CZ13 ∷ []) (refl) ▸
       at 6 12 [] (lw4 c4 (CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ CZ13 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 [] (pw2 c4 (Toff014 ∷ Toff014 ∷ []) [] tt tt Eq.refl) ▸
       at 4 2 [] (pw2 c4 (CCZ014 ∷ CCZ014 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | SBOX(3;0;42;1) @011330: 7 steps
lem-auto-CCZ012-∣-SBOX⟨3·0·42·1⟩-at011330 : Complete 4 → ⟪ (CCZ123 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CCZ123 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·0·42·1⟩-at011330 c4 = run b0
  where
  b0 : Chain (CCZ123 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ CCZ123 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ c4) ▸
       at 1 2 (Sb1-0-42-3 ∷ CCZ023 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·0·42·1⟩-at1331 c4) ▸
       at 0 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ c4) ▸
       at 1 2 (CCZ123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ023 ∷ []) (CCZ123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


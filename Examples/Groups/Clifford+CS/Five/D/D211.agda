{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D211 where

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
open import Examples.Groups.Clifford+CS.Five.D.D145 using (lem-T312-beta-at14233241 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at2442 ; lem-auto-BOX⟨0·1234⟩-∣-CS14-at2442 ; lem-auto-BOX⟨0·1234⟩-∣-CSd14-at2442 ; lem-sym12-at142142 ; lem-sym12-at2442 ; lem-sym23-at142142 ; lem-sym23-at14233142 ; lem-sym34-at14233142 ; lem-sym34-at14233241)
open import Examples.Groups.Clifford+CS.Five.D.D146 using (lem-beta-inv-at2442)
open import Examples.Groups.Clifford+CS.Five.D.D154 using (lem-X1-beta-at142142)
open import Examples.Groups.Clifford+CS.Five.D.D187 using (lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at2442 ; lem-auto-BOX⟨0·1234⟩-∣-CS13-at2442 ; lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at13213442)
open import Examples.Groups.Clifford+CS.Five.D.D192 using (lem-auto-CCZ012-∣-SBOX⟨3·2·41·0⟩-at02132031)
open import Examples.Groups.Clifford+CS.Five.D.R033 using (lem-nat-0-SBOX⟨0·1·43·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R034 using (lem-nat-0-SBOX⟨1·0·43·2⟩)
-- F5 CS13: 38 steps
lem-F5-CS13 : Complete 4 → ⟪ (X4 ∷ Sb0-1-43-2 ∷ X4 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ []) ⟫ʷ
lem-F5-CS13 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (run b4))))
  where
  b0 : Chain (X4 ∷ Sb0-1-43-2 ∷ X4 ∷ Sb0-1-43-2 ∷ []) (CCZ123 ∷ Bx0-1432 ∷ X4 ∷ Toff234 ∷ CS12 ∷ Toff234 ∷ CS12⁻ ∷ X4 ∷ Bx0-1432 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ [])
  b0 = at 1 1 (Bx0-1432 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx0-4132 ∷ []) (lem-sym12-at2442 c4) ▸
       at 0 3 (CCZ123 ∷ Bx0-4132 ∷ []) (lem-X1-beta-at142142 c4) ▸
       at 1 1 (Bx0-1432 ∷ []) (lem-sym12-at142142 c4) ▸
       at 8 1 (Bx0-1432 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ123 ∷ Bx0-1432 ∷ X4 ∷ Toff234 ∷ CS12 ∷ Toff234 ∷ CS12⁻ ∷ X4 ∷ Bx0-1432 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ []) (CCZ123 ∷ CS13 ∷ CCZ123 ∷ CS12 ∷ Toff234 ∷ Toff234 ∷ Bx0-4132 ∷ Toff234 ∷ CS12⁻ ∷ Toff234 ∷ Bx0-1432 ∷ Toff234 ∷ CS12 ∷ Toff234 ∷ CS12⁻ ∷ [])
  b1 = at 10 1 (CS12 ∷ []) (refl) ▸
       at 12 1 (CS12⁻ ∷ []) (refl) ▸
       at 2 6 (CS13 ∷ CCZ123 ∷ CS12 ∷ Toff234 ∷ CS12⁻ ∷ Toff234 ∷ []) (lw0 c4 (X4 ∷ Toff234 ∷ CS12 ∷ Toff234 ∷ CS12⁻ ∷ X4 ∷ []) (CS13 ∷ CCZ123 ∷ CS12 ∷ Toff234 ∷ CS12⁻ ∷ Toff234 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS13 ∷ Bx0-1432 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS13-at2442 c4) ▸
       at 2 2 (CCZ123 ∷ Bx0-1432 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at2442 c4) ▸
       at 3 2 (CS12 ∷ Bx0-1432 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14-at2442 c4) ▸
       at 4 0 (Toff234 ∷ Toff234 ∷ []) (lw0 c4 [] (Toff234 ∷ Toff234 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Bx0-4132 ∷ []) (lem-sym12-at2442 c4) ▸ done

  b2 : Chain (CCZ123 ∷ CS13 ∷ CCZ123 ∷ CS12 ∷ Toff234 ∷ Toff234 ∷ Bx0-4132 ∷ Toff234 ∷ CS12⁻ ∷ Toff234 ∷ Bx0-1432 ∷ Toff234 ∷ CS12 ∷ Toff234 ∷ CS12⁻ ∷ []) (CCZ123 ∷ CS13 ∷ CCZ123 ∷ CS12 ∷ Toff234 ∷ CCZ134 ∷ CS12⁻ ∷ Bx0-1432 ∷ Toff234 ∷ Bx0-1432 ∷ Toff234 ∷ CS12 ∷ Toff234 ∷ CS12⁻ ∷ [])
  b2 = at 6 1 (Bx0-4312 ∷ []) (lem-sym23-at142142 c4) ▸
       at 6 1 (Bx0-4321 ∷ []) (lem-sym34-at14233142 c4) ▸
       at 5 3 (Bx0-4321 ∷ CCZ134 ∷ []) (lem-T312-beta-at14233241 c4) ▸
       at 5 1 (Bx0-4312 ∷ []) (lem-sym34-at14233241 c4) ▸
       at 5 1 (Bx0-4132 ∷ []) (lem-sym23-at14233142 c4) ▸
       at 5 1 (Bx0-1432 ∷ []) (lem-sym12-at142142 c4) ▸
       at 5 2 (CCZ134 ∷ Bx0-1432 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at2442 c4) ▸
       at 6 2 (CS12⁻ ∷ Bx0-1432 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14-at2442 c4) ▸ done

  b3 : Chain (CCZ123 ∷ CS13 ∷ CCZ123 ∷ CS12 ∷ Toff234 ∷ CCZ134 ∷ CS12⁻ ∷ Bx0-1432 ∷ Toff234 ∷ Bx0-1432 ∷ Toff234 ∷ CS12 ∷ Toff234 ∷ CS12⁻ ∷ []) (CCZ123 ∷ CS13 ∷ CCZ123 ∷ CS12 ∷ Toff234 ∷ CCZ134 ∷ CS12⁻ ∷ Toff234 ∷ Bx0-1432 ∷ CCZ134 ∷ Bx0-1432 ∷ Toff234 ∷ CS12 ∷ Toff234 ∷ CS12⁻ ∷ [])
  b3 = at 7 0 (Toff234 ∷ Toff234 ∷ []) (lw0 c4 [] (Toff234 ∷ Toff234 ∷ []) tt tt Eq.refl) ▸
       at 9 1 (Bx0-4132 ∷ []) (lem-sym12-at2442 c4) ▸
       at 9 1 (Bx0-4312 ∷ []) (lem-sym23-at142142 c4) ▸
       at 9 1 (Bx0-4321 ∷ []) (lem-sym34-at14233142 c4) ▸
       at 8 3 (Bx0-4321 ∷ CCZ134 ∷ []) (lem-T312-beta-at14233241 c4) ▸
       at 8 1 (Bx0-4312 ∷ []) (lem-sym34-at14233241 c4) ▸
       at 8 1 (Bx0-4132 ∷ []) (lem-sym23-at14233142 c4) ▸
       at 8 1 (Bx0-1432 ∷ []) (lem-sym12-at142142 c4) ▸ done

  b4 : Chain (CCZ123 ∷ CS13 ∷ CCZ123 ∷ CS12 ∷ Toff234 ∷ CCZ134 ∷ CS12⁻ ∷ Toff234 ∷ Bx0-1432 ∷ CCZ134 ∷ Bx0-1432 ∷ Toff234 ∷ CS12 ∷ Toff234 ∷ CS12⁻ ∷ []) (CS13 ∷ [])
  b4 = at 8 2 (CCZ134 ∷ Bx0-1432 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at2442 c4) ▸
       at 1 5 (CCZ134 ∷ CS13 ∷ CCZ123 ∷ CS12 ∷ Toff234 ∷ []) (lw0 c4 (CS13 ∷ CCZ123 ∷ CS12 ∷ Toff234 ∷ CCZ134 ∷ []) (CCZ134 ∷ CS13 ∷ CCZ123 ∷ CS12 ∷ Toff234 ∷ []) tt tt Eq.refl) ▸
       at 2 7 (CCZ134 ∷ CS13 ∷ CCZ123 ∷ CS12 ∷ Toff234 ∷ CS12⁻ ∷ Toff234 ∷ []) (lw0 c4 (CS13 ∷ CCZ123 ∷ CS12 ∷ Toff234 ∷ CS12⁻ ∷ Toff234 ∷ CCZ134 ∷ []) (CCZ134 ∷ CS13 ∷ CCZ123 ∷ CS12 ∷ Toff234 ∷ CS12⁻ ∷ Toff234 ∷ []) tt tt Eq.refl) ▸
       at 1 2 [] (lw0 c4 (CCZ134 ∷ CCZ134 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 [] (lem-beta-inv-at2442 c4) ▸
       at 0 11 (CS13 ∷ []) (lw0 c4 (CCZ123 ∷ CS13 ∷ CCZ123 ∷ CS12 ∷ Toff234 ∷ CS12⁻ ∷ Toff234 ∷ Toff234 ∷ CS12 ∷ Toff234 ∷ CS12⁻ ∷ []) (CS13 ∷ []) tt tt Eq.refl) ▸ done


-- auto CS01 | SBOX(2;0;31;4) @0113203442: 7 steps
lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at0113203442 : Complete 4 → ⟪ (CS13 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-43-2 ∷ CS13 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at0113203442 c4 = run b0
  where
  b0 : Chain (CS13 ∷ Sb0-1-43-2 ∷ []) (Sb0-1-43-2 ∷ CS13 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS03 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS13 ∷ []) (CS03 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb1-0-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·43·2⟩ c4) ▸
       at 1 2 (Sb1-0-43-2 ∷ CS03 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at13213442 c4) ▸
       at 0 2 (Sb0-1-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·43·2⟩ c4) ▸
       at 1 2 (CS13 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS03 ∷ []) (CS13 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- F4 CS13^0|CS13^1: 63 steps
lem-F4-CS13ᵖ0∣CS13ᵖ1 : Complete 4 → ⟪ (X4 ∷ Sb0-1-43-2 ∷ X4 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-43-2 ∷ X4 ∷ Sb0-1-43-2 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS13ᵖ0∣CS13ᵖ1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (X4 ∷ Sb0-1-43-2 ∷ X4 ∷ Sb0-1-43-2 ∷ []) (CS13 ∷ CCZ014 ∷ Toff014 ∷ Bx1-032 ∷ Bx⁻0-12 ∷ CCZ013 ∷ Toff103 ∷ CZ12 ∷ Toff103 ∷ CCZ013 ∷ Toff014 ∷ CCZ014 ∷ [])
  b0 = at 0 4 (CS13 ∷ []) (lem-F5-CS13 c4) ▸
       at 1 0 (CCZ014 ∷ CCZ014 ∷ []) (pw2 c4 [] (CCZ014 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 2 0 (Toff014 ∷ Toff014 ∷ []) (pw2 c4 [] (Toff014 ∷ Toff014 ∷ []) tt tt Eq.refl) ▸
       at 3 0 (CCZ013 ∷ Toff103 ∷ CZ12 ∷ Toff103 ∷ CCZ013 ∷ CZ12 ∷ CZ12 ∷ CCZ013 ∷ Toff103 ∷ CZ12 ∷ Toff103 ∷ CCZ013 ∷ []) (lw4 c4 [] (CCZ013 ∷ Toff103 ∷ CZ12 ∷ Toff103 ∷ CCZ013 ∷ CZ12 ∷ CZ12 ∷ CCZ013 ∷ Toff103 ∷ CZ12 ∷ Toff103 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Bx0-12 ∷ []) (refl) ▸
       at 8 1 (Bx0-12 ∷ []) (refl) ▸
       at 3 6 (Bx1-032 ∷ []) (refl) ▸
       at 4 1 (Bx⁻0-12 ∷ []) (refl) ▸ done

  b1 : Chain (CS13 ∷ CCZ014 ∷ Toff014 ∷ Bx1-032 ∷ Bx⁻0-12 ∷ CCZ013 ∷ Toff103 ∷ CZ12 ∷ Toff103 ∷ CCZ013 ∷ Toff014 ∷ CCZ014 ∷ []) (CS13 ∷ CCZ014 ∷ Toff014 ∷ Bx1-032 ∷ Toff014 ∷ CCZ014 ∷ Bx1-032 ∷ CZ12 ∷ CCZ013 ∷ Toff103 ∷ CZ12 ∷ Toff103 ∷ CCZ013 ∷ CCZ014 ∷ Toff014 ∷ Bx⁻1-032 ∷ Toff014 ∷ CCZ014 ∷ [])
  b1 = at 7 1 (Bx⁻0-12 ∷ []) (refl) ▸
       at 4 6 (Bx⁻1-032 ∷ []) (refl) ▸
       at 4 0 (Toff014 ∷ Toff014 ∷ []) (pw2 c4 [] (Toff014 ∷ Toff014 ∷ []) tt tt Eq.refl) ▸
       at 5 0 (CCZ014 ∷ CCZ014 ∷ []) (pw2 c4 [] (CCZ014 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 6 0 (CCZ013 ∷ Toff103 ∷ CZ12 ∷ Toff103 ∷ CCZ013 ∷ CZ12 ∷ CZ12 ∷ CCZ013 ∷ Toff103 ∷ CZ12 ∷ Toff103 ∷ CCZ013 ∷ []) (lw4 c4 [] (CCZ013 ∷ Toff103 ∷ CZ12 ∷ Toff103 ∷ CCZ013 ∷ CZ12 ∷ CZ12 ∷ CCZ013 ∷ Toff103 ∷ CZ12 ∷ Toff103 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 8 1 (Bx0-12 ∷ []) (refl) ▸
       at 11 1 (Bx0-12 ∷ []) (refl) ▸
       at 6 6 (Bx1-032 ∷ []) (refl) ▸ done

  b2 : Chain (CS13 ∷ CCZ014 ∷ Toff014 ∷ Bx1-032 ∷ Toff014 ∷ CCZ014 ∷ Bx1-032 ∷ CZ12 ∷ CCZ013 ∷ Toff103 ∷ CZ12 ∷ Toff103 ∷ CCZ013 ∷ CCZ014 ∷ Toff014 ∷ Bx⁻1-032 ∷ Toff014 ∷ CCZ014 ∷ []) (CS13 ∷ Bx0-1432 ∷ Toff234 ∷ Sb0-1-2-3 ∷ CS12⁻ ∷ Toff234 ∷ Bx⁻0-1432 ∷ [])
  b2 = at 7 1 (Bx⁻0-12 ∷ []) (refl) ▸
       at 10 1 (Bx⁻0-12 ∷ []) (refl) ▸
       at 7 6 (Bx⁻1-032 ∷ []) (refl) ▸
       at 1 6 (Bx0-1432 ∷ []) (refl) ▸
       at 2 6 (Bx⁻0-1432 ∷ []) (refl) ▸
       at 2 0 (Toff234 ∷ Toff234 ∷ []) (lw0 c4 [] (Toff234 ∷ Toff234 ∷ []) tt tt Eq.refl) ▸
       at 3 0 (CS12 ∷ CS12⁻ ∷ []) (lw4 c4 [] (CS12 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb0-1-2-3 ∷ []) (refl) ▸ done

  b3 : Chain (CS13 ∷ Bx0-1432 ∷ Toff234 ∷ Sb0-1-2-3 ∷ CS12⁻ ∷ Toff234 ∷ Bx⁻0-1432 ∷ []) (Sb0-1-43-2 ∷ CS13 ∷ Sb⁻0-1-43-2 ∷ [])
  b3 = at 4 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 4 0 (Toff234 ∷ Toff234 ∷ []) (lw0 c4 [] (Toff234 ∷ Toff234 ∷ []) tt tt Eq.refl) ▸
       at 5 0 (CS12⁻ ∷ CS12 ∷ []) (lw4 c4 [] (CS12⁻ ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 6 1 (Sb0-1-2-3 ∷ []) (refl) ▸
       at 1 5 (Sb0-1-43-2 ∷ []) (refl) ▸
       at 2 5 (Sb⁻0-1-43-2 ∷ []) (refl) ▸
       at 0 2 (Sb0-1-43-2 ∷ CS13 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at0113203442 c4) ▸ done

  b4 : Chain (Sb0-1-43-2 ∷ CS13 ∷ Sb⁻0-1-43-2 ∷ []) (Sb0-1-43-2 ∷ X4 ∷ Sb0-1-43-2 ∷ X4 ∷ Bx0-1432 ∷ Toff234 ∷ CS12 ∷ Sb⁻0-1-2-3 ∷ Toff234 ∷ Bx⁻0-1432 ∷ [])
  b4 = at 1 1 (X4 ∷ Sb0-1-43-2 ∷ X4 ∷ Sb0-1-43-2 ∷ []) (sym (lem-F5-CS13 c4)) ▸
       at 5 1 (Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ Toff234 ∷ Bx⁻0-1432 ∷ []) (refl) ▸
       at 4 1 (Bx0-1432 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 8 1 (CS12⁻ ∷ []) (refl) ▸
       at 9 1 (CS12 ∷ []) (refl) ▸
       at 8 2 [] (lw4 c4 (CS12⁻ ∷ CS12 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 [] (lw0 c4 (Toff234 ∷ Toff234 ∷ []) [] tt tt Eq.refl) ▸
       at 6 1 (CS12 ∷ []) (refl) ▸ done

  b5 : Chain (Sb0-1-43-2 ∷ X4 ∷ Sb0-1-43-2 ∷ X4 ∷ Bx0-1432 ∷ Toff234 ∷ CS12 ∷ Sb⁻0-1-2-3 ∷ Toff234 ∷ Bx⁻0-1432 ∷ []) (Sb0-1-43-2 ∷ X4 ∷ Sb0-1-43-2 ∷ X4 ∷ CCZ014 ∷ Toff014 ∷ Bx1-032 ∷ Toff014 ∷ CCZ014 ∷ CCZ013 ∷ Toff103 ∷ CZ12 ∷ Toff103 ∷ CCZ013 ∷ CZ12 ∷ Bx⁻1-032 ∷ CCZ014 ∷ Toff014 ∷ Bx⁻1-032 ∷ Toff014 ∷ CCZ014 ∷ [])
  b5 = at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 6 2 [] (lw4 c4 (CS12 ∷ CS12⁻ ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 [] (lw0 c4 (Toff234 ∷ Toff234 ∷ []) [] tt tt Eq.refl) ▸
       at 5 1 (Bx⁻1-032 ∷ CCZ014 ∷ Toff014 ∷ Bx⁻1-032 ∷ Toff014 ∷ CCZ014 ∷ []) (refl) ▸
       at 4 1 (CCZ014 ∷ Toff014 ∷ Bx1-032 ∷ Toff014 ∷ CCZ014 ∷ Bx1-032 ∷ []) (refl) ▸
       at 9 1 (CCZ013 ∷ Toff103 ∷ Bx0-12 ∷ Toff103 ∷ CCZ013 ∷ Bx0-12 ∷ []) (refl) ▸
       at 11 1 (CZ12 ∷ []) (refl) ▸
       at 14 1 (CZ12 ∷ []) (refl) ▸ done

  b6 : Chain (Sb0-1-43-2 ∷ X4 ∷ Sb0-1-43-2 ∷ X4 ∷ CCZ014 ∷ Toff014 ∷ Bx1-032 ∷ Toff014 ∷ CCZ014 ∷ CCZ013 ∷ Toff103 ∷ CZ12 ∷ Toff103 ∷ CCZ013 ∷ CZ12 ∷ Bx⁻1-032 ∷ CCZ014 ∷ Toff014 ∷ Bx⁻1-032 ∷ Toff014 ∷ CCZ014 ∷ []) (Sb0-1-43-2 ∷ X4 ∷ Sb0-1-43-2 ∷ X4 ∷ CCZ014 ∷ Toff014 ∷ CCZ013 ∷ Toff103 ∷ CZ12 ∷ Toff103 ∷ CCZ013 ∷ Bx0-12 ∷ Bx⁻1-032 ∷ Toff014 ∷ CCZ014 ∷ [])
  b6 = at 15 1 (Bx⁻0-12 ∷ CCZ013 ∷ Toff103 ∷ Bx⁻0-12 ∷ Toff103 ∷ CCZ013 ∷ []) (refl) ▸
       at 15 1 (CZ12 ∷ []) (refl) ▸
       at 18 1 (CZ12 ∷ []) (refl) ▸
       at 9 12 [] (lw4 c4 (CCZ013 ∷ Toff103 ∷ CZ12 ∷ Toff103 ∷ CCZ013 ∷ CZ12 ∷ CZ12 ∷ CCZ013 ∷ Toff103 ∷ CZ12 ∷ Toff103 ∷ CCZ013 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 [] (pw2 c4 (CCZ014 ∷ CCZ014 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 [] (pw2 c4 (Toff014 ∷ Toff014 ∷ []) [] tt tt Eq.refl) ▸
       at 6 1 (CCZ013 ∷ Toff103 ∷ Bx0-12 ∷ Toff103 ∷ CCZ013 ∷ Bx0-12 ∷ []) (refl) ▸
       at 8 1 (CZ12 ∷ []) (refl) ▸ done

  b7 : Chain (Sb0-1-43-2 ∷ X4 ∷ Sb0-1-43-2 ∷ X4 ∷ CCZ014 ∷ Toff014 ∷ CCZ013 ∷ Toff103 ∷ CZ12 ∷ Toff103 ∷ CCZ013 ∷ Bx0-12 ∷ Bx⁻1-032 ∷ Toff014 ∷ CCZ014 ∷ []) (Sb0-1-43-2 ∷ X4 ∷ Sb0-1-43-2 ∷ X4 ∷ [])
  b7 = at 11 1 (CZ12 ∷ []) (refl) ▸
       at 12 1 (Bx⁻0-12 ∷ CCZ013 ∷ Toff103 ∷ Bx⁻0-12 ∷ Toff103 ∷ CCZ013 ∷ []) (refl) ▸
       at 12 1 (CZ12 ∷ []) (refl) ▸
       at 15 1 (CZ12 ∷ []) (refl) ▸
       at 6 12 [] (lw4 c4 (CCZ013 ∷ Toff103 ∷ CZ12 ∷ Toff103 ∷ CCZ013 ∷ CZ12 ∷ CZ12 ∷ CCZ013 ∷ Toff103 ∷ CZ12 ∷ Toff103 ∷ CCZ013 ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 [] (pw2 c4 (Toff014 ∷ Toff014 ∷ []) [] tt tt Eq.refl) ▸
       at 4 2 [] (pw2 c4 (CCZ014 ∷ CCZ014 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | SBOX(3;2;41;0) @02132130: 7 steps
lem-auto-CCZ012-∣-SBOX⟨3·2·41·0⟩-at02132130 : Complete 4 → ⟪ (CCZ123 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-43-2 ∷ CCZ123 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·2·41·0⟩-at02132130 c4 = run b0
  where
  b0 : Chain (CCZ123 ∷ Sb0-1-43-2 ∷ []) (Sb0-1-43-2 ∷ CCZ123 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb1-0-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·43·2⟩ c4) ▸
       at 1 2 (Sb1-0-43-2 ∷ CCZ023 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·2·41·0⟩-at02132031 c4) ▸
       at 0 2 (Sb0-1-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·43·2⟩ c4) ▸
       at 1 2 (CCZ123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ023 ∷ []) (CCZ123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


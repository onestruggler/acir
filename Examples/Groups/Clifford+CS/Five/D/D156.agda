{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D156 where

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
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-sym12-at0114203243 ; lem-sym12-at0214203143 ; lem-sym12-at14213243)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-beta-T-at0110243243)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-sym12-at0110243243 ; lem-sym12-at0210243143 ; lem-sym12-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-beta-T-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-X1-beta-at0114203243 ; lem-X1-beta-at0214203143 ; lem-X1-beta-at14213243 ; lem-beta-T-at2442)
open import Examples.Groups.Clifford+CS.Five.D.D011 using (lem-beta-T-at0210233441 ; lem-sym23-at0210233441 ; lem-sym23-at02102441 ; lem-sym34-at0210243143 ; lem-sym34-at02102441)
open import Examples.Groups.Clifford+CS.Five.D.D145 using (lem-sym12-at122441 ; lem-sym12-at142142 ; lem-sym12-at1441 ; lem-sym12-at2442)
open import Examples.Groups.Clifford+CS.Five.D.D151 using (lem-auto-CK01-∣-BOX⟨1·2034⟩)
open import Examples.Groups.Clifford+CS.Five.D.D154 using (lem-X1-beta-at01142042 ; lem-X1-beta-at142142 ; lem-X1-beta-at1441 ; lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at01122330 ; lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at011330 ; lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at02132130 ; lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at122331 ; lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at1331 ; lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at2332 ; lem-sym12-at01102442 ; lem-sym12-at01142042)
open import Examples.Groups.Clifford+CS.Five.D.D155 using (lem-auto-CS01-∣-BOX⟨2·1034⟩-at042042 ; lem-auto-CS01-∣-BOX⟨2·3014⟩-at0412203143 ; lem-auto-CS01-∣-BOX⟨2·3041⟩-at0412203143)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-BOX⟨0·2134⟩ ; lem-nat-2-BOX⟨0·1234⟩ ; lem-nat-2-BOX⟨0·1324⟩ ; lem-nat-3-BOX⟨0·1423⟩)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-3-BOX⟨0·1324⟩)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-TOFF014)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-1-BOX⟨0·1234⟩)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-0-BOX⟨0·1423⟩ ; lem-nat-1-BOX⟨1·0423⟩)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-0-BOX⟨1·0423⟩ ; lem-nat-1-BOX⟨2·0413⟩)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-nat-0-BOX⟨0·2134⟩ ; lem-nat-0-BOX⟨1·2034⟩)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-2-BOX⟨0·1432⟩)
open import Examples.Groups.Clifford+CS.Five.D.R019 using (lem-nat-2-BOX⟨0·1423⟩)
open import Examples.Groups.Clifford+CS.Five.D.R021 using (lem-nat-0-BOX⟨0·1432⟩ ; lem-nat-1-BOX⟨0·1432⟩ ; lem-nat-1-BOX⟨0·2431⟩)
open import Examples.Groups.Clifford+CS.Five.D.R022 using (lem-nat-0-BOX⟨1·0432⟩)
open import Examples.Groups.Clifford+CS.Five.D.R034 using (lem-nat-0-CK40 ; lem-nat-0-CK41 ; lem-nat-1-CK10 ; lem-nat-1-CK20 ; lem-nat-1-CK40 ; lem-nat-2-CK20 ; lem-nat-2-CK30 ; lem-nat-2-CK40 ; lem-nat-3-CK30 ; lem-nat-3-CK40)
open import Examples.Groups.Clifford+CS.Five.D.R036 using (lem-comm-CCZ123-CK40 ; lem-comm-CK40-CCZ123 ; lem-comm-CK41-TOFF203)
-- F4 S2^0|CS12^1: 24 steps
lem-F4-S2ᵖ0∣CS12ᵖ1 : Complete 4 → ⟪ (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2ᵖ0∣CS12ᵖ1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ CS24 ∷ CCZ123 ∷ X4 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b0 = at 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Bx0-4123 ∷ []) (lem-sym12-at243243 c4) ▸
       at 2 3 (CCZ123 ∷ Bx0-4123 ∷ []) (lem-X1-beta-at14213243 c4) ▸
       at 3 1 (Bx0-1423 ∷ []) (lem-sym12-at14213243 c4) ▸
       at 2 2 (Bx0-1423 ∷ CCZ123 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at01122330 c4) ▸
       at 1 2 (Bx0-1423 ∷ CS24 ∷ []) (lem-auto-CS01-∣-BOX⟨2·3014⟩-at0412203143 c4) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ CS24 ∷ CCZ123 ∷ X4 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ Toff324 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b1 = at 1 1 (Bx0-4123 ∷ []) (lem-sym12-at243243 c4) ▸
       at 0 3 (CCZ123 ∷ Bx0-4123 ∷ []) (lem-X1-beta-at14213243 c4) ▸
       at 1 1 (Bx0-1423 ∷ []) (lem-sym12-at14213243 c4) ▸
       at 0 2 (Bx0-1423 ∷ CCZ123 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at01122330 c4) ▸
       at 4 2 (X4 ∷ CCZ123 ∷ []) (lw0 c4 (CCZ123 ∷ X4 ∷ []) (X4 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (X4 ∷ CS24 ∷ X4 ∷ CCZ123 ∷ []) (lw0 c4 (CCZ123 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (CCZ123 ∷ CCZ123 ∷ []) [] tt tt Eq.refl) ▸
       at 1 4 (Toff324 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS24 ∷ X4 ∷ Toff324 ∷ []) (Toff324 ∷ X4 ∷ CS24 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Bx0-1423 ∷ Toff324 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  b2 = at 5 1 (CS13 ∷ []) (refl) ▸
       at 2 4 (CS13 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS24 ∷ X4 ∷ CS13 ∷ []) (CS13 ∷ X4 ∷ CS24 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 3 4 (Toff324 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS24 ∷ X4 ∷ Toff324 ∷ []) (Toff324 ∷ X4 ∷ CS24 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 4 4 (CS13⁻ ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS24 ∷ X4 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ X4 ∷ CS24 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done


-- F4 S2^0|CS13^1: 24 steps
lem-F4-S2ᵖ0∣CS13ᵖ1 : Complete 4 → ⟪ (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-43-2 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2ᵖ0∣CS13ᵖ1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-43-2 ∷ []) (X4 ∷ Bx0-1432 ∷ X4 ∷ X4 ∷ CS24 ∷ CCZ123 ∷ X4 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ [])
  b0 = at 3 1 (Bx0-1432 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Bx0-4132 ∷ []) (lem-sym12-at2442 c4) ▸
       at 2 3 (CCZ123 ∷ Bx0-4132 ∷ []) (lem-X1-beta-at142142 c4) ▸
       at 3 1 (Bx0-1432 ∷ []) (lem-sym12-at142142 c4) ▸
       at 2 2 (Bx0-1432 ∷ CCZ123 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at011330 c4) ▸
       at 1 2 (Bx0-1432 ∷ CS24 ∷ []) (lem-auto-CS01-∣-BOX⟨2·3041⟩-at0412203143 c4) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (X4 ∷ Bx0-1432 ∷ X4 ∷ X4 ∷ CS24 ∷ CCZ123 ∷ X4 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ []) (Bx0-1432 ∷ Toff234 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ [])
  b1 = at 1 1 (Bx0-4132 ∷ []) (lem-sym12-at2442 c4) ▸
       at 0 3 (CCZ123 ∷ Bx0-4132 ∷ []) (lem-X1-beta-at142142 c4) ▸
       at 1 1 (Bx0-1432 ∷ []) (lem-sym12-at142142 c4) ▸
       at 0 2 (Bx0-1432 ∷ CCZ123 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at011330 c4) ▸
       at 4 2 (X4 ∷ CCZ123 ∷ []) (lw0 c4 (CCZ123 ∷ X4 ∷ []) (X4 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (X4 ∷ CS24 ∷ X4 ∷ CCZ123 ∷ []) (lw0 c4 (CCZ123 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (CCZ123 ∷ CCZ123 ∷ []) [] tt tt Eq.refl) ▸
       at 1 4 (Toff234 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS24 ∷ X4 ∷ Toff234 ∷ []) (Toff234 ∷ X4 ∷ CS24 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Bx0-1432 ∷ Toff234 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ []) (Sb0-1-43-2 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  b2 = at 5 1 (CS12 ∷ []) (refl) ▸
       at 2 4 (CS12 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS24 ∷ X4 ∷ CS12 ∷ []) (CS12 ∷ X4 ∷ CS24 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb0-1-2-3 ∷ []) (refl) ▸
       at 3 4 (Toff234 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS24 ∷ X4 ∷ Toff234 ∷ []) (Toff234 ∷ X4 ∷ CS24 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 4 4 (CS12⁻ ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS24 ∷ X4 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ X4 ∷ CS24 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-43-2 ∷ []) (refl) ▸ done


-- auto CS01 | BOX(2;1034) @04122041: 7 steps
lem-auto-CS01-∣-BOX⟨2·1034⟩-at04122041 : Complete 4 → ⟪ (CS24 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ CS24 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·1034⟩-at04122041 c4 = run b0
  where
  b0 : Chain (CS24 ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ CS24 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS14 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS24 ∷ []) (CS14 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-1432 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2431⟩ c4) ▸
       at 1 2 (Bx0-1432 ∷ CS14 ∷ []) (lem-auto-CS01-∣-BOX⟨2·1034⟩-at042042 c4) ▸
       at 0 2 (Bx0-2431 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1432⟩ c4) ▸
       at 1 2 (CS24 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS14 ∷ []) (CS24 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- F4 S2^0|CS23^1: 24 steps
lem-F4-S2ᵖ0∣CS23ᵖ1 : Complete 4 → ⟪ (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2ᵖ0∣CS23ᵖ1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ CS24 ∷ CCZ123 ∷ X4 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b0 = at 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Bx0-4231 ∷ []) (lem-sym12-at122441 c4) ▸
       at 2 3 (CCZ123 ∷ Bx0-4231 ∷ []) (lem-X1-beta-at1441 c4) ▸
       at 3 1 (Bx0-2431 ∷ []) (lem-sym12-at1441 c4) ▸
       at 2 2 (Bx0-2431 ∷ CCZ123 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at02132130 c4) ▸
       at 1 2 (Bx0-2431 ∷ CS24 ∷ []) (lem-auto-CS01-∣-BOX⟨2·1034⟩-at04122041 c4) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ CS24 ∷ CCZ123 ∷ X4 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b1 = at 1 1 (Bx0-4231 ∷ []) (lem-sym12-at122441 c4) ▸
       at 0 3 (CCZ123 ∷ Bx0-4231 ∷ []) (lem-X1-beta-at1441 c4) ▸
       at 1 1 (Bx0-2431 ∷ []) (lem-sym12-at1441 c4) ▸
       at 0 2 (Bx0-2431 ∷ CCZ123 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at02132130 c4) ▸
       at 4 2 (X4 ∷ CCZ123 ∷ []) (lw0 c4 (CCZ123 ∷ X4 ∷ []) (X4 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (X4 ∷ CS24 ∷ X4 ∷ CCZ123 ∷ []) (lw0 c4 (CCZ123 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (CCZ123 ∷ CCZ123 ∷ []) [] tt tt Eq.refl) ▸
       at 1 4 (Toff134 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS24 ∷ X4 ∷ Toff134 ∷ []) (Toff134 ∷ X4 ∷ CS24 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Bx0-2431 ∷ Toff134 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  b2 = at 5 1 (CS12 ∷ []) (refl) ▸
       at 2 4 (CS12 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS24 ∷ X4 ∷ CS12 ∷ []) (CS12 ∷ X4 ∷ CS24 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 3 4 (Toff134 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS24 ∷ X4 ∷ Toff134 ∷ []) (Toff134 ∷ X4 ∷ CS24 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 4 4 (CS12⁻ ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS24 ∷ X4 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ X4 ∷ CS24 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done


-- auto CS01 | BOX(2;3041) @0413203142: 7 steps
lem-auto-CS01-∣-BOX⟨2·3041⟩-at0413203142 : Complete 4 → ⟪ (CS34 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CS34 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·3041⟩-at0413203142 c4 = run b0
  where
  b0 : Chain (CS34 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CS34 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS24 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS34 ∷ []) (CS24 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-1432 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1423⟩ c4) ▸
       at 1 2 (Bx0-1432 ∷ CS24 ∷ []) (lem-auto-CS01-∣-BOX⟨2·3041⟩-at0412203143 c4) ▸
       at 0 2 (Bx0-1423 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1432⟩ c4) ▸
       at 1 2 (CS34 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS24 ∷ []) (CS34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CS01 | BOX(2;3041) @0413213042: 7 steps
lem-auto-CS01-∣-BOX⟨2·3041⟩-at0413213042 : Complete 4 → ⟪ (CS34 ∷ Bx1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ CS34 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·3041⟩-at0413213042 c4 = run b0
  where
  b0 : Chain (CS34 ∷ Bx1-0423 ∷ []) (Bx1-0423 ∷ CS34 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS34 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑)) ▸
       at 2 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ c4) ▸
       at 1 2 (Bx0-1423 ∷ CS34 ∷ []) (lem-auto-CS01-∣-BOX⟨2·3041⟩-at0413203142 c4) ▸
       at 0 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ c4) ▸
       at 1 2 (CS34 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑)) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CS01 | BOX(2;3041) @04133041: 7 steps
lem-auto-CS01-∣-BOX⟨2·3041⟩-at04133041 : Complete 4 → ⟪ (CS34 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CS34 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·3041⟩-at04133041 c4 = run b0
  where
  b0 : Chain (CS34 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CS34 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸
       at 2 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ c4) ▸
       at 1 2 (Bx1-0423 ∷ CS34 ∷ []) (lem-auto-CS01-∣-BOX⟨2·3041⟩-at0413213042 c4) ▸
       at 0 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ c4) ▸
       at 1 2 (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- F4 S3^0|CS01^1: 24 steps
lem-F4-S3ᵖ0∣CS01ᵖ1 : Complete 4 → ⟪ (X4 ∷ CS34 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3ᵖ0∣CS01ᵖ1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CS34 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ CS34 ∷ CCZ013 ∷ X4 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b0 = at 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Bx2-4013 ∷ []) (lem-sym12-at0210243143 c4) ▸
       at 2 3 (CCZ013 ∷ Bx2-4013 ∷ []) (lem-X1-beta-at0214203143 c4) ▸
       at 3 1 (Bx2-0413 ∷ []) (lem-sym12-at0214203143 c4) ▸
       at 2 2 (Bx2-0413 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at2332 c4) ▸
       at 1 2 (Bx2-0413 ∷ CS34 ∷ []) (lem-auto-CS01-∣-BOX⟨2·3041⟩-at04133041 c4) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ CS34 ∷ CCZ013 ∷ X4 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b1 = at 1 1 (Bx2-4013 ∷ []) (lem-sym12-at0210243143 c4) ▸
       at 0 3 (CCZ013 ∷ Bx2-4013 ∷ []) (lem-X1-beta-at0214203143 c4) ▸
       at 1 1 (Bx2-0413 ∷ []) (lem-sym12-at0214203143 c4) ▸
       at 0 2 (Bx2-0413 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at2332 c4) ▸
       at 4 2 (X4 ∷ CCZ013 ∷ []) (pw2 c4 (CCZ013 ∷ X4 ∷ []) (X4 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (X4 ∷ CS34 ∷ X4 ∷ CCZ013 ∷ []) (pw2 c4 (CCZ013 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (CCZ013 ∷ CCZ013 ∷ []) [] tt tt Eq.refl) ▸
       at 1 4 (Toff314 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS34 ∷ X4 ∷ Toff314 ∷ []) (Toff314 ∷ X4 ∷ CS34 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Bx2-0413 ∷ Toff314 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  b2 = at 5 1 (CS03 ∷ []) (refl) ▸
       at 2 4 (CS03 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS34 ∷ X4 ∷ CS03 ∷ []) (CS03 ∷ X4 ∷ CS34 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 3 4 (Toff314 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS34 ∷ X4 ∷ Toff314 ∷ []) (Toff314 ∷ X4 ∷ CS34 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (CS03⁻ ∷ []) (refl) ▸
       at 4 4 (CS03⁻ ∷ X4 ∷ CS34 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS34 ∷ X4 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ X4 ∷ CS34 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done


-- F4 S3^0|CS02^1: 24 steps
lem-F4-S3ᵖ0∣CS02ᵖ1 : Complete 4 → ⟪ (X4 ∷ CS34 ∷ X4 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3ᵖ0∣CS02ᵖ1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CS34 ∷ X4 ∷ Sb1-0-42-3 ∷ []) (X4 ∷ Bx1-0423 ∷ X4 ∷ X4 ∷ CS34 ∷ CCZ023 ∷ X4 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ [])
  b0 = at 3 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Bx1-4023 ∷ []) (lem-sym12-at0110243243 c4) ▸
       at 2 3 (CCZ023 ∷ Bx1-4023 ∷ []) (lem-X1-beta-at0114203243 c4) ▸
       at 3 1 (Bx1-0423 ∷ []) (lem-sym12-at0114203243 c4) ▸
       at 2 2 (Bx1-0423 ∷ CCZ023 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at122331 c4) ▸
       at 1 2 (Bx1-0423 ∷ CS34 ∷ []) (lem-auto-CS01-∣-BOX⟨2·3041⟩-at0413213042 c4) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (X4 ∷ Bx1-0423 ∷ X4 ∷ X4 ∷ CS34 ∷ CCZ023 ∷ X4 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (Bx1-0423 ∷ Toff324 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ [])
  b1 = at 1 1 (Bx1-4023 ∷ []) (lem-sym12-at0110243243 c4) ▸
       at 0 3 (CCZ023 ∷ Bx1-4023 ∷ []) (lem-X1-beta-at0114203243 c4) ▸
       at 1 1 (Bx1-0423 ∷ []) (lem-sym12-at0114203243 c4) ▸
       at 0 2 (Bx1-0423 ∷ CCZ023 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at122331 c4) ▸
       at 4 2 (X4 ∷ CCZ023 ∷ []) (pw1 c4 (CCZ023 ∷ X4 ∷ []) (X4 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (X4 ∷ CS34 ∷ X4 ∷ CCZ023 ∷ []) (pw1 c4 (CCZ023 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (CCZ023 ∷ CCZ023 ∷ []) [] tt tt Eq.refl) ▸
       at 1 4 (Toff324 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS34 ∷ X4 ∷ Toff324 ∷ []) (Toff324 ∷ X4 ∷ CS34 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Bx1-0423 ∷ Toff324 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (Sb1-0-42-3 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  b2 = at 5 1 (CS03 ∷ []) (refl) ▸
       at 2 4 (CS03 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS34 ∷ X4 ∷ CS03 ∷ []) (CS03 ∷ X4 ∷ CS34 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb1-0-3-2 ∷ []) (refl) ▸
       at 3 4 (Toff324 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS34 ∷ X4 ∷ Toff324 ∷ []) (Toff324 ∷ X4 ∷ CS34 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (CS03⁻ ∷ []) (refl) ▸
       at 4 4 (CS03⁻ ∷ X4 ∷ CS34 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS34 ∷ X4 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ X4 ∷ CS34 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻1-0-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb1-0-42-3 ∷ []) (refl) ▸ done


-- auto CS01 | BOX(2;3014) @0413203142: 7 steps
lem-auto-CS01-∣-BOX⟨2·3014⟩-at0413203142 : Complete 4 → ⟪ (CS34 ∷ Bx0-1432 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ CS34 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·3014⟩-at0413203142 c4 = run b0
  where
  b0 : Chain (CS34 ∷ Bx0-1432 ∷ []) (Bx0-1432 ∷ CS34 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS24 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS34 ∷ []) (CS24 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-1423 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1432⟩ c4) ▸
       at 1 2 (Bx0-1423 ∷ CS24 ∷ []) (lem-auto-CS01-∣-BOX⟨2·3014⟩-at0412203143 c4) ▸
       at 0 2 (Bx0-1432 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1423⟩ c4) ▸
       at 1 2 (CS34 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS24 ∷ []) (CS34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CS01 | BOX(2;3014) @0413213042: 7 steps
lem-auto-CS01-∣-BOX⟨2·3014⟩-at0413213042 : Complete 4 → ⟪ (CS34 ∷ Bx1-0432 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0432 ∷ CS34 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·3014⟩-at0413213042 c4 = run b0
  where
  b0 : Chain (CS34 ∷ Bx1-0432 ∷ []) (Bx1-0432 ∷ CS34 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS34 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑)) ▸
       at 2 2 (Bx0-1432 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0432⟩ c4) ▸
       at 1 2 (Bx0-1432 ∷ CS34 ∷ []) (lem-auto-CS01-∣-BOX⟨2·3014⟩-at0413203142 c4) ▸
       at 0 2 (Bx1-0432 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1432⟩ c4) ▸
       at 1 2 (CS34 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑)) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- F4 S3^0|CS03^1: 24 steps
lem-F4-S3ᵖ0∣CS03ᵖ1 : Complete 4 → ⟪ (X4 ∷ CS34 ∷ X4 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-43-2 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3ᵖ0∣CS03ᵖ1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CS34 ∷ X4 ∷ Sb1-0-43-2 ∷ []) (X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ CS34 ∷ CCZ023 ∷ X4 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b0 = at 3 1 (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Bx1-4032 ∷ []) (lem-sym12-at01102442 c4) ▸
       at 2 3 (CCZ023 ∷ Bx1-4032 ∷ []) (lem-X1-beta-at01142042 c4) ▸
       at 3 1 (Bx1-0432 ∷ []) (lem-sym12-at01142042 c4) ▸
       at 2 2 (Bx1-0432 ∷ CCZ023 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at1331 c4) ▸
       at 1 2 (Bx1-0432 ∷ CS34 ∷ []) (lem-auto-CS01-∣-BOX⟨2·3014⟩-at0413213042 c4) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ CS34 ∷ CCZ023 ∷ X4 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b1 = at 1 1 (Bx1-4032 ∷ []) (lem-sym12-at01102442 c4) ▸
       at 0 3 (CCZ023 ∷ Bx1-4032 ∷ []) (lem-X1-beta-at01142042 c4) ▸
       at 1 1 (Bx1-0432 ∷ []) (lem-sym12-at01142042 c4) ▸
       at 0 2 (Bx1-0432 ∷ CCZ023 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at1331 c4) ▸
       at 4 2 (X4 ∷ CCZ023 ∷ []) (pw1 c4 (CCZ023 ∷ X4 ∷ []) (X4 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (X4 ∷ CS34 ∷ X4 ∷ CCZ023 ∷ []) (pw1 c4 (CCZ023 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (CCZ023 ∷ CCZ023 ∷ []) [] tt tt Eq.refl) ▸
       at 1 4 (Toff234 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS34 ∷ X4 ∷ Toff234 ∷ []) (Toff234 ∷ X4 ∷ CS34 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Bx1-0432 ∷ Toff234 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Sb1-0-43-2 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  b2 = at 5 1 (CS02 ∷ []) (refl) ▸
       at 2 4 (CS02 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS34 ∷ X4 ∷ CS02 ∷ []) (CS02 ∷ X4 ∷ CS34 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb1-0-2-3 ∷ []) (refl) ▸
       at 3 4 (Toff234 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS34 ∷ X4 ∷ Toff234 ∷ []) (Toff234 ∷ X4 ∷ CS34 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (CS02⁻ ∷ []) (refl) ▸
       at 4 4 (CS02⁻ ∷ X4 ∷ CS34 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS34 ∷ X4 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ X4 ∷ CS34 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 0 5 (Sb1-0-43-2 ∷ []) (refl) ▸ done


-- F4 S3^0|CS12^1: 24 steps
lem-F4-S3ᵖ0∣CS12ᵖ1 : Complete 4 → ⟪ (X4 ∷ CS34 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3ᵖ0∣CS12ᵖ1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CS34 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ CS34 ∷ CCZ123 ∷ X4 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b0 = at 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Bx0-4123 ∷ []) (lem-sym12-at243243 c4) ▸
       at 2 3 (CCZ123 ∷ Bx0-4123 ∷ []) (lem-X1-beta-at14213243 c4) ▸
       at 3 1 (Bx0-1423 ∷ []) (lem-sym12-at14213243 c4) ▸
       at 2 2 (Bx0-1423 ∷ CCZ123 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at01122330 c4) ▸
       at 1 2 (Bx0-1423 ∷ CS34 ∷ []) (lem-auto-CS01-∣-BOX⟨2·3041⟩-at0413203142 c4) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ CS34 ∷ CCZ123 ∷ X4 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ Toff324 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b1 = at 1 1 (Bx0-4123 ∷ []) (lem-sym12-at243243 c4) ▸
       at 0 3 (CCZ123 ∷ Bx0-4123 ∷ []) (lem-X1-beta-at14213243 c4) ▸
       at 1 1 (Bx0-1423 ∷ []) (lem-sym12-at14213243 c4) ▸
       at 0 2 (Bx0-1423 ∷ CCZ123 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at01122330 c4) ▸
       at 4 2 (X4 ∷ CCZ123 ∷ []) (lw0 c4 (CCZ123 ∷ X4 ∷ []) (X4 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (X4 ∷ CS34 ∷ X4 ∷ CCZ123 ∷ []) (lw0 c4 (CCZ123 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (CCZ123 ∷ CCZ123 ∷ []) [] tt tt Eq.refl) ▸
       at 1 4 (Toff324 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS34 ∷ X4 ∷ Toff324 ∷ []) (Toff324 ∷ X4 ∷ CS34 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Bx0-1423 ∷ Toff324 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  b2 = at 5 1 (CS13 ∷ []) (refl) ▸
       at 2 4 (CS13 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS34 ∷ X4 ∷ CS13 ∷ []) (CS13 ∷ X4 ∷ CS34 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 3 4 (Toff324 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS34 ∷ X4 ∷ Toff324 ∷ []) (Toff324 ∷ X4 ∷ CS34 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 4 4 (CS13⁻ ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS34 ∷ X4 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ X4 ∷ CS34 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done


-- F4 S3^0|CS13^1: 24 steps
lem-F4-S3ᵖ0∣CS13ᵖ1 : Complete 4 → ⟪ (X4 ∷ CS34 ∷ X4 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-43-2 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3ᵖ0∣CS13ᵖ1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CS34 ∷ X4 ∷ Sb0-1-43-2 ∷ []) (X4 ∷ Bx0-1432 ∷ X4 ∷ X4 ∷ CS34 ∷ CCZ123 ∷ X4 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ [])
  b0 = at 3 1 (Bx0-1432 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Bx0-4132 ∷ []) (lem-sym12-at2442 c4) ▸
       at 2 3 (CCZ123 ∷ Bx0-4132 ∷ []) (lem-X1-beta-at142142 c4) ▸
       at 3 1 (Bx0-1432 ∷ []) (lem-sym12-at142142 c4) ▸
       at 2 2 (Bx0-1432 ∷ CCZ123 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at011330 c4) ▸
       at 1 2 (Bx0-1432 ∷ CS34 ∷ []) (lem-auto-CS01-∣-BOX⟨2·3014⟩-at0413203142 c4) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (X4 ∷ Bx0-1432 ∷ X4 ∷ X4 ∷ CS34 ∷ CCZ123 ∷ X4 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ []) (Bx0-1432 ∷ Toff234 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ [])
  b1 = at 1 1 (Bx0-4132 ∷ []) (lem-sym12-at2442 c4) ▸
       at 0 3 (CCZ123 ∷ Bx0-4132 ∷ []) (lem-X1-beta-at142142 c4) ▸
       at 1 1 (Bx0-1432 ∷ []) (lem-sym12-at142142 c4) ▸
       at 0 2 (Bx0-1432 ∷ CCZ123 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at011330 c4) ▸
       at 4 2 (X4 ∷ CCZ123 ∷ []) (lw0 c4 (CCZ123 ∷ X4 ∷ []) (X4 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (X4 ∷ CS34 ∷ X4 ∷ CCZ123 ∷ []) (lw0 c4 (CCZ123 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (CCZ123 ∷ CCZ123 ∷ []) [] tt tt Eq.refl) ▸
       at 1 4 (Toff234 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS34 ∷ X4 ∷ Toff234 ∷ []) (Toff234 ∷ X4 ∷ CS34 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Bx0-1432 ∷ Toff234 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ []) (Sb0-1-43-2 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  b2 = at 5 1 (CS12 ∷ []) (refl) ▸
       at 2 4 (CS12 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS34 ∷ X4 ∷ CS12 ∷ []) (CS12 ∷ X4 ∷ CS34 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb0-1-2-3 ∷ []) (refl) ▸
       at 3 4 (Toff234 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS34 ∷ X4 ∷ Toff234 ∷ []) (Toff234 ∷ X4 ∷ CS34 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 4 4 (CS12⁻ ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS34 ∷ X4 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ X4 ∷ CS34 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-43-2 ∷ []) (refl) ▸ done


-- auto CS01 | BOX(2;3014) @0413203241: 7 steps
lem-auto-CS01-∣-BOX⟨2·3014⟩-at0413203241 : Complete 4 → ⟪ (CS34 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ CS34 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·3014⟩-at0413203241 c4 = run b0
  where
  b0 : Chain (CS34 ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ CS34 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸
       at 2 2 (Bx0-1432 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2431⟩ c4) ▸
       at 1 2 (Bx0-1432 ∷ CS34 ∷ []) (lem-auto-CS01-∣-BOX⟨2·3014⟩-at0413203142 c4) ▸
       at 0 2 (Bx0-2431 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1432⟩ c4) ▸
       at 1 2 (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- F4 S3^0|CS23^1: 24 steps
lem-F4-S3ᵖ0∣CS23ᵖ1 : Complete 4 → ⟪ (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3ᵖ0∣CS23ᵖ1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ CS34 ∷ CCZ123 ∷ X4 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b0 = at 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Bx0-4231 ∷ []) (lem-sym12-at122441 c4) ▸
       at 2 3 (CCZ123 ∷ Bx0-4231 ∷ []) (lem-X1-beta-at1441 c4) ▸
       at 3 1 (Bx0-2431 ∷ []) (lem-sym12-at1441 c4) ▸
       at 2 2 (Bx0-2431 ∷ CCZ123 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at02132130 c4) ▸
       at 1 2 (Bx0-2431 ∷ CS34 ∷ []) (lem-auto-CS01-∣-BOX⟨2·3014⟩-at0413203241 c4) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ CS34 ∷ CCZ123 ∷ X4 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b1 = at 1 1 (Bx0-4231 ∷ []) (lem-sym12-at122441 c4) ▸
       at 0 3 (CCZ123 ∷ Bx0-4231 ∷ []) (lem-X1-beta-at1441 c4) ▸
       at 1 1 (Bx0-2431 ∷ []) (lem-sym12-at1441 c4) ▸
       at 0 2 (Bx0-2431 ∷ CCZ123 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at02132130 c4) ▸
       at 4 2 (X4 ∷ CCZ123 ∷ []) (lw0 c4 (CCZ123 ∷ X4 ∷ []) (X4 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (X4 ∷ CS34 ∷ X4 ∷ CCZ123 ∷ []) (lw0 c4 (CCZ123 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (CCZ123 ∷ CCZ123 ∷ []) [] tt tt Eq.refl) ▸
       at 1 4 (Toff134 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS34 ∷ X4 ∷ Toff134 ∷ []) (Toff134 ∷ X4 ∷ CS34 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Bx0-2431 ∷ Toff134 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  b2 = at 5 1 (CS12 ∷ []) (refl) ▸
       at 2 4 (CS12 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS34 ∷ X4 ∷ CS12 ∷ []) (CS12 ∷ X4 ∷ CS34 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 3 4 (Toff134 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS34 ∷ X4 ∷ Toff134 ∷ []) (Toff134 ∷ X4 ∷ CS34 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 4 4 (CS12⁻ ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS34 ∷ X4 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ X4 ∷ CS34 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done


-- F4 K0^0|CS01^1: 18 steps
lem-F4-K0ᵖ0∣CS01ᵖ1 : Complete 4 → ⟪ (X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K0ᵖ0∣CS01ᵖ1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ X4 ∷ CK40 ∷ CCZ123 ∷ X4 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b0 = at 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 0 4 (Toff204 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CK40 ∷ X4 ∷ Toff204 ∷ []) (Toff204 ∷ X4 ∷ CK40 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ123 ∷ X4 ∷ []) (sym (c₄ (CCZ ↑) (X))) ▸
       at 2 2 (CCZ123 ∷ CK40 ∷ []) (lem-comm-CK40-CCZ123 c4) ▸
       at 1 2 (CCZ123 ∷ X4 ∷ []) (sym (c₄ (CCZ ↑) (X))) ▸
       at 2 4 (Toff204 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CK40 ∷ X4 ∷ Toff204 ∷ []) (Toff204 ∷ X4 ∷ CK40 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ123 ∷ X4 ∷ []) (sym (c₄ (CCZ ↑) (X))) ▸ done

  b1 : Chain (Toff204 ∷ CCZ123 ∷ Toff204 ∷ X4 ∷ CK40 ∷ CCZ123 ∷ X4 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b1 = at 4 2 (CCZ123 ∷ CK40 ∷ []) (lem-comm-CK40-CCZ123 c4) ▸
       at 3 2 (CCZ123 ∷ X4 ∷ []) (sym (c₄ (CCZ ↑) (X))) ▸
       at 0 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 1 4 (Toff314 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CK40 ∷ X4 ∷ Toff314 ∷ []) (Toff314 ∷ X4 ∷ CK40 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS03 ∷ []) (refl) ▸
       at 7 1 (CS03⁻ ∷ []) (refl) ▸
       at 2 6 (CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CK40 ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb2-0-3-1 ∷ []) (refl) ▸ done

  b2 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b2 = at 4 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done


-- F4 K0^0|CS02^1: 18 steps
lem-F4-K0ᵖ0∣CS02ᵖ1 : Complete 4 → ⟪ (X4 ∷ CK40 ∷ X4 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K0ᵖ0∣CS02ᵖ1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CK40 ∷ X4 ∷ Sb1-0-42-3 ∷ []) (Toff104 ∷ CCZ123 ∷ Toff104 ∷ X4 ∷ CK40 ∷ CCZ123 ∷ X4 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ [])
  b0 = at 3 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (refl) ▸
       at 3 1 (Toff104 ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ []) (lem-beta-T-at0110243243 c4) ▸
       at 0 4 (Toff104 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CK40 ∷ X4 ∷ Toff104 ∷ []) (Toff104 ∷ X4 ∷ CK40 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ123 ∷ X4 ∷ []) (sym (c₄ (CCZ ↑) (X))) ▸
       at 2 2 (CCZ123 ∷ CK40 ∷ []) (lem-comm-CK40-CCZ123 c4) ▸
       at 1 2 (CCZ123 ∷ X4 ∷ []) (sym (c₄ (CCZ ↑) (X))) ▸
       at 2 4 (Toff104 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CK40 ∷ X4 ∷ Toff104 ∷ []) (Toff104 ∷ X4 ∷ CK40 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ123 ∷ X4 ∷ []) (sym (c₄ (CCZ ↑) (X))) ▸ done

  b1 : Chain (Toff104 ∷ CCZ123 ∷ Toff104 ∷ X4 ∷ CK40 ∷ CCZ123 ∷ X4 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ CS03⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b1 = at 4 2 (CCZ123 ∷ CK40 ∷ []) (lem-comm-CK40-CCZ123 c4) ▸
       at 3 2 (CCZ123 ∷ X4 ∷ []) (sym (c₄ (CCZ ↑) (X))) ▸
       at 0 4 (Bx1-0423 ∷ []) (sym (lem-beta-T-at0110243243 c4)) ▸
       at 1 4 (Toff324 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CK40 ∷ X4 ∷ Toff324 ∷ []) (Toff324 ∷ X4 ∷ CK40 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS03 ∷ []) (refl) ▸
       at 7 1 (CS03⁻ ∷ []) (refl) ▸
       at 2 6 (CS03 ∷ Toff324 ∷ CS03⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CK40 ∷ X4 ∷ CS03 ∷ Toff324 ∷ CS03⁻ ∷ []) (CS03 ∷ Toff324 ∷ CS03⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb1-0-3-2 ∷ []) (refl) ▸ done

  b2 : Chain (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ CS03⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ []) (Sb1-0-42-3 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b2 = at 4 1 (Sb⁻1-0-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb1-0-42-3 ∷ []) (refl) ▸ done


-- beta-T @01102442: 8 steps
lem-beta-T-at01102442 : Complete 4 → ⟪ (Bx1-0432 ∷ []) ⟫ʷ ≈ ⟪ (Toff104 ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ []) ⟫ʷ
lem-beta-T-at01102442 c4 = run b0
  where
  b0 : Chain (Bx1-0432 ∷ []) (Toff104 ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1432 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0432⟩ c4) ▸
       at 1 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at2442 c4) ▸
       at 0 2 (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 c4) ▸
       at 1 2 (CCZ123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ023 ∷ []) (CCZ123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 c4) ▸
       at 3 2 (CCZ123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ023 ∷ []) (CCZ123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- F4 K0^0|CS03^1: 18 steps
lem-F4-K0ᵖ0∣CS03ᵖ1 : Complete 4 → ⟪ (X4 ∷ CK40 ∷ X4 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-43-2 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K0ᵖ0∣CS03ᵖ1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CK40 ∷ X4 ∷ Sb1-0-43-2 ∷ []) (Toff104 ∷ CCZ123 ∷ Toff104 ∷ X4 ∷ CK40 ∷ CCZ123 ∷ X4 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b0 = at 3 1 (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 3 1 (Toff104 ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ []) (lem-beta-T-at01102442 c4) ▸
       at 0 4 (Toff104 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CK40 ∷ X4 ∷ Toff104 ∷ []) (Toff104 ∷ X4 ∷ CK40 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ123 ∷ X4 ∷ []) (sym (c₄ (CCZ ↑) (X))) ▸
       at 2 2 (CCZ123 ∷ CK40 ∷ []) (lem-comm-CK40-CCZ123 c4) ▸
       at 1 2 (CCZ123 ∷ X4 ∷ []) (sym (c₄ (CCZ ↑) (X))) ▸
       at 2 4 (Toff104 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CK40 ∷ X4 ∷ Toff104 ∷ []) (Toff104 ∷ X4 ∷ CK40 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ123 ∷ X4 ∷ []) (sym (c₄ (CCZ ↑) (X))) ▸ done

  b1 : Chain (Toff104 ∷ CCZ123 ∷ Toff104 ∷ X4 ∷ CK40 ∷ CCZ123 ∷ X4 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ CS02⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b1 = at 4 2 (CCZ123 ∷ CK40 ∷ []) (lem-comm-CK40-CCZ123 c4) ▸
       at 3 2 (CCZ123 ∷ X4 ∷ []) (sym (c₄ (CCZ ↑) (X))) ▸
       at 0 4 (Bx1-0432 ∷ []) (sym (lem-beta-T-at01102442 c4)) ▸
       at 1 4 (Toff234 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CK40 ∷ X4 ∷ Toff234 ∷ []) (Toff234 ∷ X4 ∷ CK40 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS02 ∷ []) (refl) ▸
       at 7 1 (CS02⁻ ∷ []) (refl) ▸
       at 2 6 (CS02 ∷ Toff234 ∷ CS02⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CK40 ∷ X4 ∷ CS02 ∷ Toff234 ∷ CS02⁻ ∷ []) (CS02 ∷ Toff234 ∷ CS02⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb1-0-2-3 ∷ []) (refl) ▸ done

  b2 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ CS02⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ []) (Sb1-0-43-2 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b2 = at 4 1 (Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 0 5 (Sb1-0-43-2 ∷ []) (refl) ▸ done


-- auto CK01 | BOX(1;2034) @0110: 7 steps
lem-auto-CK01-∣-BOX⟨1·2034⟩-at0110 : Complete 4 → ⟪ (CK10 ∷ Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ CK10 ∷ []) ⟫ʷ
lem-auto-CK01-∣-BOX⟨1·2034⟩-at0110 c4 = run b0
  where
  b0 : Chain (CK10 ∷ Bx0-2134 ∷ []) (Bx0-2134 ∷ CK10 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CK01 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CK10 ∷ []) (CK01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx1-2034 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2134⟩ c4) ▸
       at 1 2 (Bx1-2034 ∷ CK01 ∷ []) (lem-auto-CK01-∣-BOX⟨1·2034⟩ c4) ▸
       at 0 2 (Bx0-2134 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2034⟩ c4) ▸
       at 1 2 (CK10 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CK01 ∷ []) (CK10 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CK01 | BOX(1;2034) @021021: 7 steps
lem-auto-CK01-∣-BOX⟨1·2034⟩-at021021 : Complete 4 → ⟪ (CK20 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CK20 ∷ []) ⟫ʷ
lem-auto-CK01-∣-BOX⟨1·2034⟩-at021021 c4 = run b0
  where
  b0 : Chain (CK20 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CK20 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CK10 ∷ Sw12 ∷ []) (lem-nat-1-CK20 c4) ▸
       at 2 2 (Bx0-2134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1234⟩ c4) ▸
       at 1 2 (Bx0-2134 ∷ CK10 ∷ []) (lem-auto-CK01-∣-BOX⟨1·2034⟩-at0110 c4) ▸
       at 0 2 (Bx0-1234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2134⟩ c4) ▸
       at 1 2 (CK20 ∷ Sw12 ∷ []) (lem-nat-1-CK10 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CK01 | BOX(1;2034) @03102132: 7 steps
lem-auto-CK01-∣-BOX⟨1·2034⟩-at03102132 : Complete 4 → ⟪ (CK30 ∷ Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ CK30 ∷ []) ⟫ʷ
lem-auto-CK01-∣-BOX⟨1·2034⟩-at03102132 c4 = run b0
  where
  b0 : Chain (CK30 ∷ Bx0-1324 ∷ []) (Bx0-1324 ∷ CK30 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CK20 ∷ Sw23 ∷ []) (lem-nat-2-CK30 c4) ▸
       at 2 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ c4) ▸
       at 1 2 (Bx0-1234 ∷ CK20 ∷ []) (lem-auto-CK01-∣-BOX⟨1·2034⟩-at021021 c4) ▸
       at 0 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ c4) ▸
       at 1 2 (CK30 ∷ Sw23 ∷ []) (lem-nat-2-CK20 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CK01 | BOX(1;2034) @0410213243: 7 steps
lem-auto-CK01-∣-BOX⟨1·2034⟩-at0410213243 : Complete 4 → ⟪ (CK40 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CK40 ∷ []) ⟫ʷ
lem-auto-CK01-∣-BOX⟨1·2034⟩-at0410213243 c4 = run b0
  where
  b0 : Chain (CK40 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CK40 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CK30 ∷ Sw34 ∷ []) (lem-nat-3-CK40 c4) ▸
       at 2 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ c4) ▸
       at 1 2 (Bx0-1324 ∷ CK30 ∷ []) (lem-auto-CK01-∣-BOX⟨1·2034⟩-at03102132 c4) ▸
       at 0 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ c4) ▸
       at 1 2 (CK40 ∷ Sw34 ∷ []) (lem-nat-3-CK30 c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- F4 K0^0|CS12^1: 26 steps
lem-F4-K0ᵖ0∣CS12ᵖ1 : Complete 4 → ⟪ (X4 ∷ CK40 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K0ᵖ0∣CS12ᵖ1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (X4 ∷ CK40 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ CK40 ∷ CCZ123 ∷ X4 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b0 = at 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Bx0-4123 ∷ []) (lem-sym12-at243243 c4) ▸
       at 2 3 (CCZ123 ∷ Bx0-4123 ∷ []) (lem-X1-beta-at14213243 c4) ▸
       at 3 1 (Bx0-1423 ∷ []) (lem-sym12-at14213243 c4) ▸
       at 2 2 (Bx0-1423 ∷ CCZ123 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at01122330 c4) ▸
       at 1 2 (Bx0-1423 ∷ CK40 ∷ []) (lem-auto-CK01-∣-BOX⟨1·2034⟩-at0410213243 c4) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (X4 ∷ Bx0-1423 ∷ X4 ∷ X4 ∷ CK40 ∷ CCZ123 ∷ X4 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ X4 ∷ CK40 ∷ X4 ∷ CCZ123 ∷ CCZ123 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b1 = at 1 1 (Bx0-4123 ∷ []) (lem-sym12-at243243 c4) ▸
       at 0 3 (CCZ123 ∷ Bx0-4123 ∷ []) (lem-X1-beta-at14213243 c4) ▸
       at 1 1 (Bx0-1423 ∷ []) (lem-sym12-at14213243 c4) ▸
       at 0 2 (Bx0-1423 ∷ CCZ123 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at01122330 c4) ▸
       at 4 2 (X4 ∷ CCZ123 ∷ []) (lw0 c4 (CCZ123 ∷ X4 ∷ []) (X4 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (X4 ∷ CCZ123 ∷ []) (c₄ (CCZ ↑) (X)) ▸
       at 2 2 (CK40 ∷ CCZ123 ∷ []) (lem-comm-CCZ123-CK40 c4) ▸
       at 3 2 (X4 ∷ CCZ123 ∷ []) (c₄ (CCZ ↑) (X)) ▸ done

  b2 : Chain (Bx0-1423 ∷ X4 ∷ CK40 ∷ X4 ∷ CCZ123 ∷ CCZ123 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b2 = at 4 2 [] (lw4 c4 (CCZ123 ∷ CCZ123 ∷ []) [] tt tt Eq.refl) ▸
       at 1 4 (Toff324 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CK40 ∷ X4 ∷ Toff324 ∷ []) (Toff324 ∷ X4 ∷ CK40 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS13 ∷ []) (refl) ▸
       at 2 4 (CS13 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CK40 ∷ X4 ∷ CS13 ∷ []) (CS13 ∷ X4 ∷ CK40 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 3 4 (Toff324 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CK40 ∷ X4 ∷ Toff324 ∷ []) (Toff324 ∷ X4 ∷ CK40 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 4 4 (CS13⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CK40 ∷ X4 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b3 : Chain (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b3 = at 4 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done


-- auto CK01 | BOX(1;2034) @04102142: 7 steps
lem-auto-CK01-∣-BOX⟨1·2034⟩-at04102142 : Complete 4 → ⟪ (CK40 ∷ Bx0-1432 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ CK40 ∷ []) ⟫ʷ
lem-auto-CK01-∣-BOX⟨1·2034⟩-at04102142 c4 = run b0
  where
  b0 : Chain (CK40 ∷ Bx0-1432 ∷ []) (Bx0-1432 ∷ CK40 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CK40 ∷ Sw23 ∷ []) (lem-nat-2-CK40 c4) ▸
       at 2 2 (Bx0-1423 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1432⟩ c4) ▸
       at 1 2 (Bx0-1423 ∷ CK40 ∷ []) (lem-auto-CK01-∣-BOX⟨1·2034⟩-at0410213243 c4) ▸
       at 0 2 (Bx0-1432 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1423⟩ c4) ▸
       at 1 2 (CK40 ∷ Sw23 ∷ []) (lem-nat-2-CK40 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- F4 K0^0|CS13^1: 26 steps
lem-F4-K0ᵖ0∣CS13ᵖ1 : Complete 4 → ⟪ (X4 ∷ CK40 ∷ X4 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-43-2 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K0ᵖ0∣CS13ᵖ1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (X4 ∷ CK40 ∷ X4 ∷ Sb0-1-43-2 ∷ []) (X4 ∷ Bx0-1432 ∷ X4 ∷ X4 ∷ CK40 ∷ CCZ123 ∷ X4 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ [])
  b0 = at 3 1 (Bx0-1432 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Bx0-4132 ∷ []) (lem-sym12-at2442 c4) ▸
       at 2 3 (CCZ123 ∷ Bx0-4132 ∷ []) (lem-X1-beta-at142142 c4) ▸
       at 3 1 (Bx0-1432 ∷ []) (lem-sym12-at142142 c4) ▸
       at 2 2 (Bx0-1432 ∷ CCZ123 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at011330 c4) ▸
       at 1 2 (Bx0-1432 ∷ CK40 ∷ []) (lem-auto-CK01-∣-BOX⟨1·2034⟩-at04102142 c4) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (X4 ∷ Bx0-1432 ∷ X4 ∷ X4 ∷ CK40 ∷ CCZ123 ∷ X4 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ []) (Bx0-1432 ∷ X4 ∷ CK40 ∷ X4 ∷ CCZ123 ∷ CCZ123 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ [])
  b1 = at 1 1 (Bx0-4132 ∷ []) (lem-sym12-at2442 c4) ▸
       at 0 3 (CCZ123 ∷ Bx0-4132 ∷ []) (lem-X1-beta-at142142 c4) ▸
       at 1 1 (Bx0-1432 ∷ []) (lem-sym12-at142142 c4) ▸
       at 0 2 (Bx0-1432 ∷ CCZ123 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at011330 c4) ▸
       at 4 2 (X4 ∷ CCZ123 ∷ []) (lw0 c4 (CCZ123 ∷ X4 ∷ []) (X4 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (X4 ∷ CCZ123 ∷ []) (c₄ (CCZ ↑) (X)) ▸
       at 2 2 (CK40 ∷ CCZ123 ∷ []) (lem-comm-CCZ123-CK40 c4) ▸
       at 3 2 (X4 ∷ CCZ123 ∷ []) (c₄ (CCZ ↑) (X)) ▸ done

  b2 : Chain (Bx0-1432 ∷ X4 ∷ CK40 ∷ X4 ∷ CCZ123 ∷ CCZ123 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ []) (Bx0-1432 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ CS12⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b2 = at 4 2 [] (lw4 c4 (CCZ123 ∷ CCZ123 ∷ []) [] tt tt Eq.refl) ▸
       at 1 4 (Toff234 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CK40 ∷ X4 ∷ Toff234 ∷ []) (Toff234 ∷ X4 ∷ CK40 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS12 ∷ []) (refl) ▸
       at 2 4 (CS12 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CK40 ∷ X4 ∷ CS12 ∷ []) (CS12 ∷ X4 ∷ CK40 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb0-1-2-3 ∷ []) (refl) ▸
       at 3 4 (Toff234 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CK40 ∷ X4 ∷ Toff234 ∷ []) (Toff234 ∷ X4 ∷ CK40 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 4 4 (CS12⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CK40 ∷ X4 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b3 : Chain (Bx0-1432 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ CS12⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ []) (Sb0-1-43-2 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b3 = at 4 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-43-2 ∷ []) (refl) ▸ done


-- auto CK01 | BOX(1;2034) @041041: 7 steps
lem-auto-CK01-∣-BOX⟨1·2034⟩-at041041 : Complete 4 → ⟪ (CK40 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ CK40 ∷ []) ⟫ʷ
lem-auto-CK01-∣-BOX⟨1·2034⟩-at041041 c4 = run b0
  where
  b0 : Chain (CK40 ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ CK40 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CK40 ∷ Sw12 ∷ []) (lem-nat-1-CK40 c4) ▸
       at 2 2 (Bx0-1432 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2431⟩ c4) ▸
       at 1 2 (Bx0-1432 ∷ CK40 ∷ []) (lem-auto-CK01-∣-BOX⟨1·2034⟩-at04102142 c4) ▸
       at 0 2 (Bx0-2431 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1432⟩ c4) ▸
       at 1 2 (CK40 ∷ Sw12 ∷ []) (lem-nat-1-CK40 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- F4 K0^0|CS23^1: 26 steps
lem-F4-K0ᵖ0∣CS23ᵖ1 : Complete 4 → ⟪ (X4 ∷ CK40 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K0ᵖ0∣CS23ᵖ1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (X4 ∷ CK40 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ CK40 ∷ CCZ123 ∷ X4 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b0 = at 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Bx0-4231 ∷ []) (lem-sym12-at122441 c4) ▸
       at 2 3 (CCZ123 ∷ Bx0-4231 ∷ []) (lem-X1-beta-at1441 c4) ▸
       at 3 1 (Bx0-2431 ∷ []) (lem-sym12-at1441 c4) ▸
       at 2 2 (Bx0-2431 ∷ CCZ123 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at02132130 c4) ▸
       at 1 2 (Bx0-2431 ∷ CK40 ∷ []) (lem-auto-CK01-∣-BOX⟨1·2034⟩-at041041 c4) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ CK40 ∷ CCZ123 ∷ X4 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ X4 ∷ CK40 ∷ X4 ∷ CCZ123 ∷ CCZ123 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b1 = at 1 1 (Bx0-4231 ∷ []) (lem-sym12-at122441 c4) ▸
       at 0 3 (CCZ123 ∷ Bx0-4231 ∷ []) (lem-X1-beta-at1441 c4) ▸
       at 1 1 (Bx0-2431 ∷ []) (lem-sym12-at1441 c4) ▸
       at 0 2 (Bx0-2431 ∷ CCZ123 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at02132130 c4) ▸
       at 4 2 (X4 ∷ CCZ123 ∷ []) (lw0 c4 (CCZ123 ∷ X4 ∷ []) (X4 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (X4 ∷ CCZ123 ∷ []) (c₄ (CCZ ↑) (X)) ▸
       at 2 2 (CK40 ∷ CCZ123 ∷ []) (lem-comm-CCZ123-CK40 c4) ▸
       at 3 2 (X4 ∷ CCZ123 ∷ []) (c₄ (CCZ ↑) (X)) ▸ done

  b2 : Chain (Bx0-2431 ∷ X4 ∷ CK40 ∷ X4 ∷ CCZ123 ∷ CCZ123 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b2 = at 4 2 [] (lw4 c4 (CCZ123 ∷ CCZ123 ∷ []) [] tt tt Eq.refl) ▸
       at 1 4 (Toff134 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CK40 ∷ X4 ∷ Toff134 ∷ []) (Toff134 ∷ X4 ∷ CK40 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS12 ∷ []) (refl) ▸
       at 2 4 (CS12 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CK40 ∷ X4 ∷ CS12 ∷ []) (CS12 ∷ X4 ∷ CK40 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 3 4 (Toff134 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CK40 ∷ X4 ∷ Toff134 ∷ []) (Toff134 ∷ X4 ∷ CK40 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 4 4 (CS12⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CK40 ∷ X4 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b3 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b3 = at 4 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done


-- F4 K1^0|CS01^1: 24 steps
lem-F4-K1ᵖ0∣CS01ᵖ1 : Complete 4 → ⟪ (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K1ᵖ0∣CS01ᵖ1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Toff203 ∷ CCZ124 ∷ X4 ∷ CK41 ∷ X4 ∷ Toff203 ∷ CCZ124 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b0 = at 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (Bx2-0431 ∷ []) (lem-sym34-at0210243143 c4) ▸
       at 3 1 (Bx2-0341 ∷ []) (lem-sym23-at02102441 c4) ▸
       at 3 1 (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-beta-T-at0210233441 c4) ▸
       at 2 2 (Toff203 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 1 2 (Toff203 ∷ CK41 ∷ []) (lem-comm-CK41-TOFF203 c4) ▸
       at 0 2 (Toff203 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 1 4 (CCZ124 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK41 ∷ X4 ∷ CCZ124 ∷ []) (CCZ124 ∷ X4 ∷ CK41 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Toff203 ∷ CCZ124 ∷ X4 ∷ CK41 ∷ X4 ∷ Toff203 ∷ CCZ124 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b1 = at 4 2 (Toff203 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 3 2 (Toff203 ∷ CK41 ∷ []) (lem-comm-CK41-TOFF203 c4) ▸
       at 2 2 (Toff203 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 3 4 (CCZ124 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK41 ∷ X4 ∷ CCZ124 ∷ []) (CCZ124 ∷ X4 ∷ CK41 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx2-0341 ∷ []) (sym (lem-beta-T-at0210233441 c4)) ▸
       at 0 1 (Bx2-0431 ∷ []) (lem-sym23-at0210233441 c4) ▸
       at 0 1 (Bx2-0413 ∷ []) (lem-sym34-at02102441 c4) ▸
       at 1 4 (Toff314 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK41 ∷ X4 ∷ Toff314 ∷ []) (Toff314 ∷ X4 ∷ CK41 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Bx2-0413 ∷ Toff314 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b2 = at 5 1 (CS03 ∷ []) (refl) ▸
       at 2 4 (CS03 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CK41 ∷ X4 ∷ CS03 ∷ []) (CS03 ∷ X4 ∷ CK41 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 3 4 (Toff314 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK41 ∷ X4 ∷ Toff314 ∷ []) (Toff314 ∷ X4 ∷ CK41 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (CS03⁻ ∷ []) (refl) ▸
       at 4 4 (CS03⁻ ∷ X4 ∷ CK41 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CK41 ∷ X4 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ X4 ∷ CK41 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done


-- auto CK01 | BOX(1;2034) @04203243: 7 steps
lem-auto-CK01-∣-BOX⟨1·2034⟩-at04203243 : Complete 4 → ⟪ (CK41 ∷ Bx1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ CK41 ∷ []) ⟫ʷ
lem-auto-CK01-∣-BOX⟨1·2034⟩-at04203243 c4 = run b0
  where
  b0 : Chain (CK41 ∷ Bx1-0423 ∷ []) (Bx1-0423 ∷ CK41 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CK40 ∷ Sw01 ∷ []) (lem-nat-0-CK41 c4) ▸
       at 2 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ c4) ▸
       at 1 2 (Bx0-1423 ∷ CK40 ∷ []) (lem-auto-CK01-∣-BOX⟨1·2034⟩-at0410213243 c4) ▸
       at 0 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ c4) ▸
       at 1 2 (CK41 ∷ Sw01 ∷ []) (lem-nat-0-CK40 c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


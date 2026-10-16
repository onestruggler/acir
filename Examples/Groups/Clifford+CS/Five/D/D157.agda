{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D157 where

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
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-beta-T-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-sym12-at0114203243 ; lem-sym12-at0214203143)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-sym23-at0110243243 ; lem-sym23-at01103443 ; lem-sym23-at12213443 ; lem-sym23-at12243143 ; lem-sym23-at243243 ; lem-sym23-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-sym12-at0110243243 ; lem-sym12-at0210243143 ; lem-sym23-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-beta-T-at0210243143 ; lem-sym23-at0210213443)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-X1-beta-at0114203243 ; lem-X1-beta-at0214203143 ; lem-beta-T-at2442)
open import Examples.Groups.Clifford+CS.Five.D.D011 using (lem-beta-T-at0110233442 ; lem-beta-T-at01103443 ; lem-beta-T-at0210213443 ; lem-beta-T-at233442 ; lem-beta-T-at3443 ; lem-sym23-at0110233442 ; lem-sym23-at01102442 ; lem-sym23-at233442 ; lem-sym23-at2442 ; lem-sym34-at0110243243 ; lem-sym34-at01102442 ; lem-sym34-at243243 ; lem-sym34-at2442)
open import Examples.Groups.Clifford+CS.Five.D.D153 using (lem-sym34-at12243143)
open import Examples.Groups.Clifford+CS.Five.D.D154 using (lem-X1-beta-at01142042 ; lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at122331 ; lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at1331 ; lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at2332 ; lem-sym12-at01102442 ; lem-sym12-at01142042)
open import Examples.Groups.Clifford+CS.Five.D.D156 using (lem-auto-CK01-∣-BOX⟨1·2034⟩-at04102142 ; lem-auto-CK01-∣-BOX⟨1·2034⟩-at04203243)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-CCZ023 ; lem-nat-1-CCZ024 ; lem-nat-1-CCZ034 ; lem-nat-1-TOFF014)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-1-BOX⟨0·1423⟩)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-1-BOX⟨1·0423⟩ ; lem-nat-1-TOFF013)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-1-BOX⟨2·0413⟩)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-nat-1-BOX⟨0·2143⟩)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-nat-1-BOX⟨0·1342⟩ ; lem-nat-1-BOX⟨0·2341⟩)
open import Examples.Groups.Clifford+CS.Five.D.R021 using (lem-nat-0-BOX⟨0·1432⟩ ; lem-nat-1-BOX⟨0·1432⟩ ; lem-nat-1-BOX⟨0·2431⟩)
open import Examples.Groups.Clifford+CS.Five.D.R022 using (lem-nat-0-BOX⟨1·0432⟩)
open import Examples.Groups.Clifford+CS.Five.D.R034 using (lem-nat-0-CK40 ; lem-nat-0-CK41)
open import Examples.Groups.Clifford+CS.Five.D.R036 using (lem-comm-CCZ013-CK42 ; lem-comm-CCZ023-CK41 ; lem-comm-CK41-CCZ023 ; lem-comm-CK41-TOFF023 ; lem-comm-CK42-CCZ013 ; lem-comm-CK42-TOFF013 ; lem-comm-CK42-TOFF103)
-- F4 K1^0|CS02^1: 26 steps
lem-F4-K1ᵖ0∣CS02ᵖ1 : Complete 4 → ⟪ (X4 ∷ CK41 ∷ X4 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K1ᵖ0∣CS02ᵖ1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ Sb1-0-42-3 ∷ []) (X4 ∷ Bx1-0423 ∷ X4 ∷ X4 ∷ CK41 ∷ CCZ023 ∷ X4 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ [])
  b0 = at 3 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Bx1-4023 ∷ []) (lem-sym12-at0110243243 c4) ▸
       at 2 3 (CCZ023 ∷ Bx1-4023 ∷ []) (lem-X1-beta-at0114203243 c4) ▸
       at 3 1 (Bx1-0423 ∷ []) (lem-sym12-at0114203243 c4) ▸
       at 2 2 (Bx1-0423 ∷ CCZ023 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at122331 c4) ▸
       at 1 2 (Bx1-0423 ∷ CK41 ∷ []) (lem-auto-CK01-∣-BOX⟨1·2034⟩-at04203243 c4) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (X4 ∷ Bx1-0423 ∷ X4 ∷ X4 ∷ CK41 ∷ CCZ023 ∷ X4 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (Bx1-0423 ∷ X4 ∷ CK41 ∷ X4 ∷ CCZ023 ∷ CCZ023 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ [])
  b1 = at 1 1 (Bx1-4023 ∷ []) (lem-sym12-at0110243243 c4) ▸
       at 0 3 (CCZ023 ∷ Bx1-4023 ∷ []) (lem-X1-beta-at0114203243 c4) ▸
       at 1 1 (Bx1-0423 ∷ []) (lem-sym12-at0114203243 c4) ▸
       at 0 2 (Bx1-0423 ∷ CCZ023 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at122331 c4) ▸
       at 4 2 (X4 ∷ CCZ023 ∷ []) (pw1 c4 (CCZ023 ∷ X4 ∷ []) (X4 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (X4 ∷ CCZ023 ∷ []) (c₄ (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) (X)) ▸
       at 2 2 (CK41 ∷ CCZ023 ∷ []) (lem-comm-CCZ023-CK41 c4) ▸
       at 3 2 (X4 ∷ CCZ023 ∷ []) (c₄ (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) (X)) ▸ done

  b2 : Chain (Bx1-0423 ∷ X4 ∷ CK41 ∷ X4 ∷ CCZ023 ∷ CCZ023 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ CS03⁻ ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b2 = at 4 2 [] (lw4 c4 (CCZ023 ∷ CCZ023 ∷ []) [] tt tt Eq.refl) ▸
       at 1 4 (Toff324 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK41 ∷ X4 ∷ Toff324 ∷ []) (Toff324 ∷ X4 ∷ CK41 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS03 ∷ []) (refl) ▸
       at 2 4 (CS03 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CK41 ∷ X4 ∷ CS03 ∷ []) (CS03 ∷ X4 ∷ CK41 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb1-0-3-2 ∷ []) (refl) ▸
       at 3 4 (Toff324 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK41 ∷ X4 ∷ Toff324 ∷ []) (Toff324 ∷ X4 ∷ CK41 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (CS03⁻ ∷ []) (refl) ▸
       at 4 4 (CS03⁻ ∷ X4 ∷ CK41 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CK41 ∷ X4 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ X4 ∷ CK41 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b3 : Chain (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ CS03⁻ ∷ X4 ∷ CK41 ∷ X4 ∷ []) (Sb1-0-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b3 = at 4 1 (Sb⁻1-0-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb1-0-42-3 ∷ []) (refl) ▸ done


-- auto CK01 | BOX(1;2034) @042042: 7 steps
lem-auto-CK01-∣-BOX⟨1·2034⟩-at042042 : Complete 4 → ⟪ (CK41 ∷ Bx1-0432 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0432 ∷ CK41 ∷ []) ⟫ʷ
lem-auto-CK01-∣-BOX⟨1·2034⟩-at042042 c4 = run b0
  where
  b0 : Chain (CK41 ∷ Bx1-0432 ∷ []) (Bx1-0432 ∷ CK41 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CK40 ∷ Sw01 ∷ []) (lem-nat-0-CK41 c4) ▸
       at 2 2 (Bx0-1432 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0432⟩ c4) ▸
       at 1 2 (Bx0-1432 ∷ CK40 ∷ []) (lem-auto-CK01-∣-BOX⟨1·2034⟩-at04102142 c4) ▸
       at 0 2 (Bx1-0432 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1432⟩ c4) ▸
       at 1 2 (CK41 ∷ Sw01 ∷ []) (lem-nat-0-CK40 c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- F4 K1^0|CS03^1: 26 steps
lem-F4-K1ᵖ0∣CS03ᵖ1 : Complete 4 → ⟪ (X4 ∷ CK41 ∷ X4 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-43-2 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K1ᵖ0∣CS03ᵖ1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ Sb1-0-43-2 ∷ []) (X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ CK41 ∷ CCZ023 ∷ X4 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b0 = at 3 1 (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Bx1-4032 ∷ []) (lem-sym12-at01102442 c4) ▸
       at 2 3 (CCZ023 ∷ Bx1-4032 ∷ []) (lem-X1-beta-at01142042 c4) ▸
       at 3 1 (Bx1-0432 ∷ []) (lem-sym12-at01142042 c4) ▸
       at 2 2 (Bx1-0432 ∷ CCZ023 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at1331 c4) ▸
       at 1 2 (Bx1-0432 ∷ CK41 ∷ []) (lem-auto-CK01-∣-BOX⟨1·2034⟩-at042042 c4) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (X4 ∷ Bx1-0432 ∷ X4 ∷ X4 ∷ CK41 ∷ CCZ023 ∷ X4 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ X4 ∷ CK41 ∷ X4 ∷ CCZ023 ∷ CCZ023 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b1 = at 1 1 (Bx1-4032 ∷ []) (lem-sym12-at01102442 c4) ▸
       at 0 3 (CCZ023 ∷ Bx1-4032 ∷ []) (lem-X1-beta-at01142042 c4) ▸
       at 1 1 (Bx1-0432 ∷ []) (lem-sym12-at01142042 c4) ▸
       at 0 2 (Bx1-0432 ∷ CCZ023 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at1331 c4) ▸
       at 4 2 (X4 ∷ CCZ023 ∷ []) (pw1 c4 (CCZ023 ∷ X4 ∷ []) (X4 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (X4 ∷ CCZ023 ∷ []) (c₄ (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) (X)) ▸
       at 2 2 (CK41 ∷ CCZ023 ∷ []) (lem-comm-CCZ023-CK41 c4) ▸
       at 3 2 (X4 ∷ CCZ023 ∷ []) (c₄ (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) (X)) ▸ done

  b2 : Chain (Bx1-0432 ∷ X4 ∷ CK41 ∷ X4 ∷ CCZ023 ∷ CCZ023 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ CS02⁻ ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b2 = at 4 2 [] (lw4 c4 (CCZ023 ∷ CCZ023 ∷ []) [] tt tt Eq.refl) ▸
       at 1 4 (Toff234 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK41 ∷ X4 ∷ Toff234 ∷ []) (Toff234 ∷ X4 ∷ CK41 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS02 ∷ []) (refl) ▸
       at 2 4 (CS02 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CK41 ∷ X4 ∷ CS02 ∷ []) (CS02 ∷ X4 ∷ CK41 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb1-0-2-3 ∷ []) (refl) ▸
       at 3 4 (Toff234 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK41 ∷ X4 ∷ Toff234 ∷ []) (Toff234 ∷ X4 ∷ CK41 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (CS02⁻ ∷ []) (refl) ▸
       at 4 4 (CS02⁻ ∷ X4 ∷ CK41 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CK41 ∷ X4 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ X4 ∷ CK41 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b3 : Chain (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ CS02⁻ ∷ X4 ∷ CK41 ∷ X4 ∷ []) (Sb1-0-43-2 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b3 = at 4 1 (Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 0 5 (Sb1-0-43-2 ∷ []) (refl) ▸ done


-- F4 K1^0|CS12^1: 18 steps
lem-F4-K1ᵖ0∣CS12ᵖ1 : Complete 4 → ⟪ (X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K1ᵖ0∣CS12ᵖ1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ X4 ∷ CK41 ∷ CCZ023 ∷ X4 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b0 = at 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at243243 c4) ▸
       at 0 4 (Toff014 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CK41 ∷ X4 ∷ Toff014 ∷ []) (Toff014 ∷ X4 ∷ CK41 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 2 2 (CCZ023 ∷ CK41 ∷ []) (lem-comm-CK41-CCZ023 c4) ▸
       at 1 2 (CCZ023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 2 4 (Toff014 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CK41 ∷ X4 ∷ Toff014 ∷ []) (Toff014 ∷ X4 ∷ CK41 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) (X))) ▸ done

  b1 : Chain (Toff014 ∷ CCZ023 ∷ Toff014 ∷ X4 ∷ CK41 ∷ CCZ023 ∷ X4 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b1 = at 4 2 (CCZ023 ∷ CK41 ∷ []) (lem-comm-CK41-CCZ023 c4) ▸
       at 3 2 (CCZ023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 0 4 (Bx0-1423 ∷ []) (sym (lem-beta-T-at243243 c4)) ▸
       at 1 4 (Toff324 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK41 ∷ X4 ∷ Toff324 ∷ []) (Toff324 ∷ X4 ∷ CK41 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS13 ∷ []) (refl) ▸
       at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 2 6 (CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK41 ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CK41 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb0-1-3-2 ∷ []) (refl) ▸ done

  b2 : Chain (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CK41 ∷ X4 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b2 = at 4 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done


-- F4 K1^0|CS13^1: 18 steps
lem-F4-K1ᵖ0∣CS13ᵖ1 : Complete 4 → ⟪ (X4 ∷ CK41 ∷ X4 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-43-2 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K1ᵖ0∣CS13ᵖ1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ Sb0-1-43-2 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ X4 ∷ CK41 ∷ CCZ023 ∷ X4 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ [])
  b0 = at 3 1 (Bx0-1432 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 3 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at2442 c4) ▸
       at 0 4 (Toff014 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CK41 ∷ X4 ∷ Toff014 ∷ []) (Toff014 ∷ X4 ∷ CK41 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 2 2 (CCZ023 ∷ CK41 ∷ []) (lem-comm-CK41-CCZ023 c4) ▸
       at 1 2 (CCZ023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 2 4 (Toff014 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CK41 ∷ X4 ∷ Toff014 ∷ []) (Toff014 ∷ X4 ∷ CK41 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) (X))) ▸ done

  b1 : Chain (Toff014 ∷ CCZ023 ∷ Toff014 ∷ X4 ∷ CK41 ∷ CCZ023 ∷ X4 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ []) (Bx0-1432 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ CS12⁻ ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b1 = at 4 2 (CCZ023 ∷ CK41 ∷ []) (lem-comm-CK41-CCZ023 c4) ▸
       at 3 2 (CCZ023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 0 4 (Bx0-1432 ∷ []) (sym (lem-beta-T-at2442 c4)) ▸
       at 1 4 (Toff234 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK41 ∷ X4 ∷ Toff234 ∷ []) (Toff234 ∷ X4 ∷ CK41 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS12 ∷ []) (refl) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 2 6 (CS12 ∷ Toff234 ∷ CS12⁻ ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK41 ∷ X4 ∷ CS12 ∷ Toff234 ∷ CS12⁻ ∷ []) (CS12 ∷ Toff234 ∷ CS12⁻ ∷ X4 ∷ CK41 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb0-1-2-3 ∷ []) (refl) ▸ done

  b2 : Chain (Bx0-1432 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ CS12⁻ ∷ X4 ∷ CK41 ∷ X4 ∷ []) (Sb0-1-43-2 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b2 = at 4 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-43-2 ∷ []) (refl) ▸ done


-- sym23 @122441: 5 steps
lem-sym23-at122441 : Complete 4 → ⟪ (Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ []) ⟫ʷ
lem-sym23-at122441 c4 = run b0
  where
  b0 : Chain (Bx0-2431 ∷ []) (Bx0-2341 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1432 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2431⟩ c4) ▸
       at 1 1 (Bx0-1342 ∷ []) (lem-sym23-at2442 c4) ▸
       at 0 2 (Bx0-2341 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1342⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- beta-T @12233441: 8 steps
lem-beta-T-at12233441 : Complete 4 → ⟪ (Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) ⟫ʷ
lem-beta-T-at12233441 c4 = run b0
  where
  b0 : Chain (Bx0-2341 ∷ []) (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1342 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2341⟩ c4) ▸
       at 1 1 (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-beta-T-at233442 c4) ▸
       at 0 2 (Toff023 ∷ Sw12 ∷ []) (lem-nat-1-TOFF013 c4) ▸
       at 1 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 2 2 (Toff023 ∷ Sw12 ∷ []) (lem-nat-1-TOFF013 c4) ▸
       at 3 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 4 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @12233441: 5 steps
lem-sym23-at12233441 : Complete 4 → ⟪ (Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ []) ⟫ʷ
lem-sym23-at12233441 c4 = run b0
  where
  b0 : Chain (Bx0-2341 ∷ []) (Bx0-2431 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1342 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2341⟩ c4) ▸
       at 1 1 (Bx0-1432 ∷ []) (lem-sym23-at233442 c4) ▸
       at 0 2 (Bx0-2431 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1432⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- F4 K1^0|CS23^1: 20 steps
lem-F4-K1ᵖ0∣CS23ᵖ1 : Complete 4 → ⟪ (X4 ∷ CK41 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K1ᵖ0∣CS23ᵖ1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Toff023 ∷ CCZ014 ∷ X4 ∷ CK41 ∷ Toff023 ∷ X4 ∷ CCZ014 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b0 = at 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 1 (Bx0-2341 ∷ []) (lem-sym23-at122441 c4) ▸
       at 3 1 (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) (lem-beta-T-at12233441 c4) ▸
       at 2 2 (Toff023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 1 2 (Toff023 ∷ CK41 ∷ []) (lem-comm-CK41-TOFF023 c4) ▸
       at 0 2 (Toff023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 1 4 (CCZ014 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CK41 ∷ X4 ∷ CCZ014 ∷ []) (CCZ014 ∷ X4 ∷ CK41 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (X))) ▸ done

  b1 : Chain (Toff023 ∷ CCZ014 ∷ X4 ∷ CK41 ∷ Toff023 ∷ X4 ∷ CCZ014 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ X4 ∷ CK41 ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b1 = at 3 2 (Toff023 ∷ CK41 ∷ []) (lem-comm-CK41-TOFF023 c4) ▸
       at 2 2 (Toff023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 3 4 (CCZ014 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CK41 ∷ X4 ∷ CCZ014 ∷ []) (CCZ014 ∷ X4 ∷ CK41 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx0-2341 ∷ []) (sym (lem-beta-T-at12233441 c4)) ▸
       at 0 1 (Bx0-2431 ∷ []) (lem-sym23-at12233441 c4) ▸
       at 1 4 (Toff134 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK41 ∷ X4 ∷ Toff134 ∷ []) (Toff134 ∷ X4 ∷ CK41 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS12 ∷ []) (refl) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸ done

  b2 : Chain (Bx0-2431 ∷ Toff134 ∷ X4 ∷ CK41 ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b2 = at 2 6 (CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK41 ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CK41 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done


-- auto CK01 | BOX(1;2034) @0412203143: 7 steps
lem-auto-CK01-∣-BOX⟨1·2034⟩-at0412203143 : Complete 4 → ⟪ (CK42 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CK42 ∷ []) ⟫ʷ
lem-auto-CK01-∣-BOX⟨1·2034⟩-at0412203143 c4 = run b0
  where
  b0 : Chain (CK42 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CK42 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CK41 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CK42 ∷ []) (CK41 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ c4) ▸
       at 1 2 (Bx1-0423 ∷ CK41 ∷ []) (lem-auto-CK01-∣-BOX⟨1·2034⟩-at04203243 c4) ▸
       at 0 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ c4) ▸
       at 1 2 (CK42 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CK41 ∷ []) (CK42 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- F4 K2^0|CS01^1: 26 steps
lem-F4-K2ᵖ0∣CS01ᵖ1 : Complete 4 → ⟪ (X4 ∷ CK42 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2ᵖ0∣CS01ᵖ1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ CK42 ∷ CCZ013 ∷ X4 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b0 = at 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Bx2-4013 ∷ []) (lem-sym12-at0210243143 c4) ▸
       at 2 3 (CCZ013 ∷ Bx2-4013 ∷ []) (lem-X1-beta-at0214203143 c4) ▸
       at 3 1 (Bx2-0413 ∷ []) (lem-sym12-at0214203143 c4) ▸
       at 2 2 (Bx2-0413 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at2332 c4) ▸
       at 1 2 (Bx2-0413 ∷ CK42 ∷ []) (lem-auto-CK01-∣-BOX⟨1·2034⟩-at0412203143 c4) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ CK42 ∷ CCZ013 ∷ X4 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ X4 ∷ CK42 ∷ X4 ∷ CCZ013 ∷ CCZ013 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b1 = at 1 1 (Bx2-4013 ∷ []) (lem-sym12-at0210243143 c4) ▸
       at 0 3 (CCZ013 ∷ Bx2-4013 ∷ []) (lem-X1-beta-at0214203143 c4) ▸
       at 1 1 (Bx2-0413 ∷ []) (lem-sym12-at0214203143 c4) ▸
       at 0 2 (Bx2-0413 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0412⟩-at2332 c4) ▸
       at 4 2 (X4 ∷ CCZ013 ∷ []) (pw2 c4 (CCZ013 ∷ X4 ∷ []) (X4 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (X4 ∷ CCZ013 ∷ []) (c₄ (Swap ↑ ↑ • CCZ • Swap ↑ ↑) (X)) ▸
       at 2 2 (CK42 ∷ CCZ013 ∷ []) (lem-comm-CCZ013-CK42 c4) ▸
       at 3 2 (X4 ∷ CCZ013 ∷ []) (c₄ (Swap ↑ ↑ • CCZ • Swap ↑ ↑) (X)) ▸ done

  b2 : Chain (Bx2-0413 ∷ X4 ∷ CK42 ∷ X4 ∷ CCZ013 ∷ CCZ013 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b2 = at 4 2 [] (lw4 c4 (CCZ013 ∷ CCZ013 ∷ []) [] tt tt Eq.refl) ▸
       at 1 4 (Toff314 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK42 ∷ X4 ∷ Toff314 ∷ []) (Toff314 ∷ X4 ∷ CK42 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS03 ∷ []) (refl) ▸
       at 2 4 (CS03 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CK42 ∷ X4 ∷ CS03 ∷ []) (CS03 ∷ X4 ∷ CK42 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 3 4 (Toff314 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK42 ∷ X4 ∷ Toff314 ∷ []) (Toff314 ∷ X4 ∷ CK42 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (CS03⁻ ∷ []) (refl) ▸
       at 4 4 (CS03⁻ ∷ X4 ∷ CK42 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CK42 ∷ X4 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ X4 ∷ CK42 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b3 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CK42 ∷ X4 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b3 = at 4 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done


-- F4 K2^0|CS02^1: 24 steps
lem-F4-K2ᵖ0∣CS02ᵖ1 : Complete 4 → ⟪ (X4 ∷ CK42 ∷ X4 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2ᵖ0∣CS02ᵖ1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ Sb1-0-42-3 ∷ []) (Toff103 ∷ CCZ124 ∷ X4 ∷ CK42 ∷ X4 ∷ Toff103 ∷ CCZ124 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ [])
  b0 = at 3 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (refl) ▸
       at 3 1 (Bx1-0432 ∷ []) (lem-sym34-at0110243243 c4) ▸
       at 3 1 (Bx1-0342 ∷ []) (lem-sym23-at01102442 c4) ▸
       at 3 1 (Toff103 ∷ CCZ124 ∷ Toff103 ∷ CCZ124 ∷ []) (lem-beta-T-at0110233442 c4) ▸
       at 2 2 (Toff103 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) (X))) ▸
       at 1 2 (Toff103 ∷ CK42 ∷ []) (lem-comm-CK42-TOFF103 c4) ▸
       at 0 2 (Toff103 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) (X))) ▸
       at 1 4 (CCZ124 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK42 ∷ X4 ∷ CCZ124 ∷ []) (CCZ124 ∷ X4 ∷ CK42 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Toff103 ∷ CCZ124 ∷ X4 ∷ CK42 ∷ X4 ∷ Toff103 ∷ CCZ124 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (Bx1-0423 ∷ Toff324 ∷ X4 ∷ CK42 ∷ X4 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ [])
  b1 = at 4 2 (Toff103 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) (X))) ▸
       at 3 2 (Toff103 ∷ CK42 ∷ []) (lem-comm-CK42-TOFF103 c4) ▸
       at 2 2 (Toff103 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) (X))) ▸
       at 3 4 (CCZ124 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK42 ∷ X4 ∷ CCZ124 ∷ []) (CCZ124 ∷ X4 ∷ CK42 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx1-0342 ∷ []) (sym (lem-beta-T-at0110233442 c4)) ▸
       at 0 1 (Bx1-0432 ∷ []) (lem-sym23-at0110233442 c4) ▸
       at 0 1 (Bx1-0423 ∷ []) (lem-sym34-at01102442 c4) ▸
       at 1 4 (Toff324 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK42 ∷ X4 ∷ Toff324 ∷ []) (Toff324 ∷ X4 ∷ CK42 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Bx1-0423 ∷ Toff324 ∷ X4 ∷ CK42 ∷ X4 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (Sb1-0-42-3 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b2 = at 5 1 (CS03 ∷ []) (refl) ▸
       at 2 4 (CS03 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CK42 ∷ X4 ∷ CS03 ∷ []) (CS03 ∷ X4 ∷ CK42 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb1-0-3-2 ∷ []) (refl) ▸
       at 3 4 (Toff324 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK42 ∷ X4 ∷ Toff324 ∷ []) (Toff324 ∷ X4 ∷ CK42 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (CS03⁻ ∷ []) (refl) ▸
       at 4 4 (CS03⁻ ∷ X4 ∷ CK42 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CK42 ∷ X4 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ X4 ∷ CK42 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻1-0-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb1-0-42-3 ∷ []) (refl) ▸ done


-- F4 K2^0|CS03^1: 20 steps
lem-F4-K2ᵖ0∣CS03ᵖ1 : Complete 4 → ⟪ (X4 ∷ CK42 ∷ X4 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-43-2 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2ᵖ0∣CS03ᵖ1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ Sb1-0-43-2 ∷ []) (Toff103 ∷ CCZ124 ∷ X4 ∷ CK42 ∷ Toff103 ∷ X4 ∷ CCZ124 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b0 = at 3 1 (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 3 1 (Bx1-0342 ∷ []) (lem-sym23-at01102442 c4) ▸
       at 3 1 (Toff103 ∷ CCZ124 ∷ Toff103 ∷ CCZ124 ∷ []) (lem-beta-T-at0110233442 c4) ▸
       at 2 2 (Toff103 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) (X))) ▸
       at 1 2 (Toff103 ∷ CK42 ∷ []) (lem-comm-CK42-TOFF103 c4) ▸
       at 0 2 (Toff103 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) (X))) ▸
       at 1 4 (CCZ124 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK42 ∷ X4 ∷ CCZ124 ∷ []) (CCZ124 ∷ X4 ∷ CK42 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff103 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) (X))) ▸ done

  b1 : Chain (Toff103 ∷ CCZ124 ∷ X4 ∷ CK42 ∷ Toff103 ∷ X4 ∷ CCZ124 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ X4 ∷ CK42 ∷ X4 ∷ CS02 ∷ Toff234 ∷ CS02⁻ ∷ [])
  b1 = at 3 2 (Toff103 ∷ CK42 ∷ []) (lem-comm-CK42-TOFF103 c4) ▸
       at 2 2 (Toff103 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) (X))) ▸
       at 3 4 (CCZ124 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK42 ∷ X4 ∷ CCZ124 ∷ []) (CCZ124 ∷ X4 ∷ CK42 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx1-0342 ∷ []) (sym (lem-beta-T-at0110233442 c4)) ▸
       at 0 1 (Bx1-0432 ∷ []) (lem-sym23-at0110233442 c4) ▸
       at 1 4 (Toff234 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK42 ∷ X4 ∷ Toff234 ∷ []) (Toff234 ∷ X4 ∷ CK42 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS02 ∷ []) (refl) ▸
       at 7 1 (CS02⁻ ∷ []) (refl) ▸ done

  b2 : Chain (Bx1-0432 ∷ Toff234 ∷ X4 ∷ CK42 ∷ X4 ∷ CS02 ∷ Toff234 ∷ CS02⁻ ∷ []) (Sb1-0-43-2 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b2 = at 2 6 (CS02 ∷ Toff234 ∷ CS02⁻ ∷ X4 ∷ CK42 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CK42 ∷ X4 ∷ CS02 ∷ Toff234 ∷ CS02⁻ ∷ []) (CS02 ∷ Toff234 ∷ CS02⁻ ∷ X4 ∷ CK42 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb1-0-2-3 ∷ []) (refl) ▸
       at 4 1 (Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 0 5 (Sb1-0-43-2 ∷ []) (refl) ▸ done


-- F4 K2^0|CS12^1: 24 steps
lem-F4-K2ᵖ0∣CS12ᵖ1 : Complete 4 → ⟪ (X4 ∷ CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2ᵖ0∣CS12ᵖ1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Toff013 ∷ CCZ024 ∷ X4 ∷ CK42 ∷ X4 ∷ Toff013 ∷ CCZ024 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b0 = at 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 1 (Bx0-1432 ∷ []) (lem-sym34-at243243 c4) ▸
       at 3 1 (Bx0-1342 ∷ []) (lem-sym23-at2442 c4) ▸
       at 3 1 (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-beta-T-at233442 c4) ▸
       at 2 2 (Toff013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))) ▸
       at 1 2 (Toff013 ∷ CK42 ∷ []) (lem-comm-CK42-TOFF013 c4) ▸
       at 0 2 (Toff013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))) ▸
       at 1 4 (CCZ024 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CK42 ∷ X4 ∷ CCZ024 ∷ []) (CCZ024 ∷ X4 ∷ CK42 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Toff013 ∷ CCZ024 ∷ X4 ∷ CK42 ∷ X4 ∷ Toff013 ∷ CCZ024 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ Toff324 ∷ X4 ∷ CK42 ∷ X4 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b1 = at 4 2 (Toff013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))) ▸
       at 3 2 (Toff013 ∷ CK42 ∷ []) (lem-comm-CK42-TOFF013 c4) ▸
       at 2 2 (Toff013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))) ▸
       at 3 4 (CCZ024 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CK42 ∷ X4 ∷ CCZ024 ∷ []) (CCZ024 ∷ X4 ∷ CK42 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx0-1342 ∷ []) (sym (lem-beta-T-at233442 c4)) ▸
       at 0 1 (Bx0-1432 ∷ []) (lem-sym23-at233442 c4) ▸
       at 0 1 (Bx0-1423 ∷ []) (lem-sym34-at2442 c4) ▸
       at 1 4 (Toff324 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK42 ∷ X4 ∷ Toff324 ∷ []) (Toff324 ∷ X4 ∷ CK42 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Bx0-1423 ∷ Toff324 ∷ X4 ∷ CK42 ∷ X4 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b2 = at 5 1 (CS13 ∷ []) (refl) ▸
       at 2 4 (CS13 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK42 ∷ X4 ∷ CS13 ∷ []) (CS13 ∷ X4 ∷ CK42 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 3 4 (Toff324 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK42 ∷ X4 ∷ Toff324 ∷ []) (Toff324 ∷ X4 ∷ CK42 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 4 4 (CS13⁻ ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK42 ∷ X4 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ X4 ∷ CK42 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done


-- F4 K2^0|CS13^1: 20 steps
lem-F4-K2ᵖ0∣CS13ᵖ1 : Complete 4 → ⟪ (X4 ∷ CK42 ∷ X4 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-43-2 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2ᵖ0∣CS13ᵖ1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ Sb0-1-43-2 ∷ []) (Toff013 ∷ CCZ024 ∷ X4 ∷ CK42 ∷ Toff013 ∷ X4 ∷ CCZ024 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ [])
  b0 = at 3 1 (Bx0-1432 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 3 1 (Bx0-1342 ∷ []) (lem-sym23-at2442 c4) ▸
       at 3 1 (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-beta-T-at233442 c4) ▸
       at 2 2 (Toff013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))) ▸
       at 1 2 (Toff013 ∷ CK42 ∷ []) (lem-comm-CK42-TOFF013 c4) ▸
       at 0 2 (Toff013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))) ▸
       at 1 4 (CCZ024 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CK42 ∷ X4 ∷ CCZ024 ∷ []) (CCZ024 ∷ X4 ∷ CK42 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))) ▸ done

  b1 : Chain (Toff013 ∷ CCZ024 ∷ X4 ∷ CK42 ∷ Toff013 ∷ X4 ∷ CCZ024 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ []) (Bx0-1432 ∷ Toff234 ∷ X4 ∷ CK42 ∷ X4 ∷ CS12 ∷ Toff234 ∷ CS12⁻ ∷ [])
  b1 = at 3 2 (Toff013 ∷ CK42 ∷ []) (lem-comm-CK42-TOFF013 c4) ▸
       at 2 2 (Toff013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))) ▸
       at 3 4 (CCZ024 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CK42 ∷ X4 ∷ CCZ024 ∷ []) (CCZ024 ∷ X4 ∷ CK42 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx0-1342 ∷ []) (sym (lem-beta-T-at233442 c4)) ▸
       at 0 1 (Bx0-1432 ∷ []) (lem-sym23-at233442 c4) ▸
       at 1 4 (Toff234 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK42 ∷ X4 ∷ Toff234 ∷ []) (Toff234 ∷ X4 ∷ CK42 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS12 ∷ []) (refl) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸ done

  b2 : Chain (Bx0-1432 ∷ Toff234 ∷ X4 ∷ CK42 ∷ X4 ∷ CS12 ∷ Toff234 ∷ CS12⁻ ∷ []) (Sb0-1-43-2 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b2 = at 2 6 (CS12 ∷ Toff234 ∷ CS12⁻ ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK42 ∷ X4 ∷ CS12 ∷ Toff234 ∷ CS12⁻ ∷ []) (CS12 ∷ Toff234 ∷ CS12⁻ ∷ X4 ∷ CK42 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb0-1-2-3 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-43-2 ∷ []) (refl) ▸ done


-- beta-T @122441: 8 steps
lem-beta-T-at122441 : Complete 4 → ⟪ (Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) ⟫ʷ
lem-beta-T-at122441 c4 = run b0
  where
  b0 : Chain (Bx0-2431 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1432 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2431⟩ c4) ▸
       at 1 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at2442 c4) ▸
       at 0 2 (Toff024 ∷ Sw12 ∷ []) (lem-nat-1-TOFF014 c4) ▸
       at 1 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 2 2 (Toff024 ∷ Sw12 ∷ []) (lem-nat-1-TOFF014 c4) ▸
       at 3 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 4 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- F4 K2^0|CS23^1: 18 steps
lem-F4-K2ᵖ0∣CS23ᵖ1 : Complete 4 → ⟪ (X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2ᵖ0∣CS23ᵖ1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ X4 ∷ CK42 ∷ CCZ013 ∷ X4 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b0 = at 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-beta-T-at122441 c4) ▸
       at 0 4 (Toff024 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CK42 ∷ X4 ∷ Toff024 ∷ []) (Toff024 ∷ X4 ∷ CK42 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • CCZ • Swap ↑ ↑) (X))) ▸
       at 2 2 (CCZ013 ∷ CK42 ∷ []) (lem-comm-CK42-CCZ013 c4) ▸
       at 1 2 (CCZ013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • CCZ • Swap ↑ ↑) (X))) ▸
       at 2 4 (Toff024 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CK42 ∷ X4 ∷ Toff024 ∷ []) (Toff024 ∷ X4 ∷ CK42 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • CCZ • Swap ↑ ↑) (X))) ▸ done

  b1 : Chain (Toff024 ∷ CCZ013 ∷ Toff024 ∷ X4 ∷ CK42 ∷ CCZ013 ∷ X4 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b1 = at 4 2 (CCZ013 ∷ CK42 ∷ []) (lem-comm-CK42-CCZ013 c4) ▸
       at 3 2 (CCZ013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • CCZ • Swap ↑ ↑) (X))) ▸
       at 0 4 (Bx0-2431 ∷ []) (sym (lem-beta-T-at122441 c4)) ▸
       at 1 4 (Toff134 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK42 ∷ X4 ∷ Toff134 ∷ []) (Toff134 ∷ X4 ∷ CK42 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS12 ∷ []) (refl) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 2 6 (CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK42 ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CK42 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb0-2-1-3 ∷ []) (refl) ▸ done

  b2 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CK42 ∷ X4 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b2 = at 4 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done


-- F4 K3^0|CS01^1: 20 steps
lem-F4-K3ᵖ0∣CS01ᵖ1 : Complete 4 → ⟪ (X4 ∷ CK43 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3ᵖ0∣CS01ᵖ1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CK43 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Toff201 ∷ CCZ234 ∷ X4 ∷ CK43 ∷ Toff201 ∷ X4 ∷ CCZ234 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b0 = at 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4) ▸
       at 3 1 (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-beta-T-at0210213443 c4) ▸
       at 2 2 (Toff201 ∷ X4 ∷ []) (sym (c₃ (Toffᵗ) (X ↑))) ▸
       at 1 2 (Toff201 ∷ CK43 ∷ []) (sym (c₃ (Toffᵗ) (CK₁₀))) ▸
       at 0 2 (Toff201 ∷ X4 ∷ []) (sym (c₃ (Toffᵗ) (X ↑))) ▸
       at 1 4 (CCZ234 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK43 ∷ X4 ∷ CCZ234 ∷ []) (CCZ234 ∷ X4 ∷ CK43 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff201 ∷ X4 ∷ []) (sym (c₃ (Toffᵗ) (X ↑))) ▸ done

  b1 : Chain (Toff201 ∷ CCZ234 ∷ X4 ∷ CK43 ∷ Toff201 ∷ X4 ∷ CCZ234 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ Toff314 ∷ X4 ∷ CK43 ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b1 = at 3 2 (Toff201 ∷ CK43 ∷ []) (sym (c₃ (Toffᵗ) (CK₁₀))) ▸
       at 2 2 (Toff201 ∷ X4 ∷ []) (sym (c₃ (Toffᵗ) (X ↑))) ▸
       at 3 4 (CCZ234 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK43 ∷ X4 ∷ CCZ234 ∷ []) (CCZ234 ∷ X4 ∷ CK43 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx2-0143 ∷ []) (sym (lem-beta-T-at0210213443 c4)) ▸
       at 0 1 (Bx2-0413 ∷ []) (lem-sym23-at0210213443 c4) ▸
       at 1 4 (Toff314 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK43 ∷ X4 ∷ Toff314 ∷ []) (Toff314 ∷ X4 ∷ CK43 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS03 ∷ []) (refl) ▸
       at 7 1 (CS03⁻ ∷ []) (refl) ▸ done

  b2 : Chain (Bx2-0413 ∷ Toff314 ∷ X4 ∷ CK43 ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  b2 = at 2 6 (CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CK43 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CK43 ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CK43 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done


-- F4 K3^0|CS02^1: 20 steps
lem-F4-K3ᵖ0∣CS02ᵖ1 : Complete 4 → ⟪ (X4 ∷ CK43 ∷ X4 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3ᵖ0∣CS02ᵖ1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CK43 ∷ X4 ∷ Sb1-0-42-3 ∷ []) (Toff102 ∷ CCZ134 ∷ X4 ∷ CK43 ∷ Toff102 ∷ X4 ∷ CCZ134 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ [])
  b0 = at 3 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (refl) ▸
       at 3 1 (Bx1-0243 ∷ []) (lem-sym23-at0110243243 c4) ▸
       at 3 1 (Toff102 ∷ CCZ134 ∷ Toff102 ∷ CCZ134 ∷ []) (lem-beta-T-at01103443 c4) ▸
       at 2 2 (Toff102 ∷ X4 ∷ []) (sym (c₃ (K ↑ • CCZ • K ↑ • iI) (X ↑))) ▸
       at 1 2 (Toff102 ∷ CK43 ∷ []) (sym (c₃ (K ↑ • CCZ • K ↑ • iI) (CK₁₀))) ▸
       at 0 2 (Toff102 ∷ X4 ∷ []) (sym (c₃ (K ↑ • CCZ • K ↑ • iI) (X ↑))) ▸
       at 1 4 (CCZ134 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK43 ∷ X4 ∷ CCZ134 ∷ []) (CCZ134 ∷ X4 ∷ CK43 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff102 ∷ X4 ∷ []) (sym (c₃ (K ↑ • CCZ • K ↑ • iI) (X ↑))) ▸ done

  b1 : Chain (Toff102 ∷ CCZ134 ∷ X4 ∷ CK43 ∷ Toff102 ∷ X4 ∷ CCZ134 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (Bx1-0423 ∷ Toff324 ∷ X4 ∷ CK43 ∷ X4 ∷ CS03 ∷ Toff324 ∷ CS03⁻ ∷ [])
  b1 = at 3 2 (Toff102 ∷ CK43 ∷ []) (sym (c₃ (K ↑ • CCZ • K ↑ • iI) (CK₁₀))) ▸
       at 2 2 (Toff102 ∷ X4 ∷ []) (sym (c₃ (K ↑ • CCZ • K ↑ • iI) (X ↑))) ▸
       at 3 4 (CCZ134 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK43 ∷ X4 ∷ CCZ134 ∷ []) (CCZ134 ∷ X4 ∷ CK43 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx1-0243 ∷ []) (sym (lem-beta-T-at01103443 c4)) ▸
       at 0 1 (Bx1-0423 ∷ []) (lem-sym23-at01103443 c4) ▸
       at 1 4 (Toff324 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK43 ∷ X4 ∷ Toff324 ∷ []) (Toff324 ∷ X4 ∷ CK43 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS03 ∷ []) (refl) ▸
       at 7 1 (CS03⁻ ∷ []) (refl) ▸ done

  b2 : Chain (Bx1-0423 ∷ Toff324 ∷ X4 ∷ CK43 ∷ X4 ∷ CS03 ∷ Toff324 ∷ CS03⁻ ∷ []) (Sb1-0-42-3 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  b2 = at 2 6 (CS03 ∷ Toff324 ∷ CS03⁻ ∷ X4 ∷ CK43 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CK43 ∷ X4 ∷ CS03 ∷ Toff324 ∷ CS03⁻ ∷ []) (CS03 ∷ Toff324 ∷ CS03⁻ ∷ X4 ∷ CK43 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb1-0-3-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻1-0-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb1-0-42-3 ∷ []) (refl) ▸ done


-- F4 K3^0|CS03^1: 24 steps
lem-F4-K3ᵖ0∣CS03ᵖ1 : Complete 4 → ⟪ (X4 ∷ CK43 ∷ X4 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-43-2 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3ᵖ0∣CS03ᵖ1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CK43 ∷ X4 ∷ Sb1-0-43-2 ∷ []) (Toff102 ∷ CCZ134 ∷ X4 ∷ CK43 ∷ X4 ∷ Toff102 ∷ CCZ134 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b0 = at 3 1 (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 3 1 (Bx1-0423 ∷ []) (lem-sym34-at01102442 c4) ▸
       at 3 1 (Bx1-0243 ∷ []) (lem-sym23-at0110243243 c4) ▸
       at 3 1 (Toff102 ∷ CCZ134 ∷ Toff102 ∷ CCZ134 ∷ []) (lem-beta-T-at01103443 c4) ▸
       at 2 2 (Toff102 ∷ X4 ∷ []) (sym (c₃ (K ↑ • CCZ • K ↑ • iI) (X ↑))) ▸
       at 1 2 (Toff102 ∷ CK43 ∷ []) (sym (c₃ (K ↑ • CCZ • K ↑ • iI) (CK₁₀))) ▸
       at 0 2 (Toff102 ∷ X4 ∷ []) (sym (c₃ (K ↑ • CCZ • K ↑ • iI) (X ↑))) ▸
       at 1 4 (CCZ134 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK43 ∷ X4 ∷ CCZ134 ∷ []) (CCZ134 ∷ X4 ∷ CK43 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Toff102 ∷ CCZ134 ∷ X4 ∷ CK43 ∷ X4 ∷ Toff102 ∷ CCZ134 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Bx1-0432 ∷ Toff234 ∷ X4 ∷ CK43 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b1 = at 4 2 (Toff102 ∷ X4 ∷ []) (sym (c₃ (K ↑ • CCZ • K ↑ • iI) (X ↑))) ▸
       at 3 2 (Toff102 ∷ CK43 ∷ []) (sym (c₃ (K ↑ • CCZ • K ↑ • iI) (CK₁₀))) ▸
       at 2 2 (Toff102 ∷ X4 ∷ []) (sym (c₃ (K ↑ • CCZ • K ↑ • iI) (X ↑))) ▸
       at 3 4 (CCZ134 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK43 ∷ X4 ∷ CCZ134 ∷ []) (CCZ134 ∷ X4 ∷ CK43 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx1-0243 ∷ []) (sym (lem-beta-T-at01103443 c4)) ▸
       at 0 1 (Bx1-0423 ∷ []) (lem-sym23-at01103443 c4) ▸
       at 0 1 (Bx1-0432 ∷ []) (lem-sym34-at0110243243 c4) ▸
       at 1 4 (Toff234 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK43 ∷ X4 ∷ Toff234 ∷ []) (Toff234 ∷ X4 ∷ CK43 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Bx1-0432 ∷ Toff234 ∷ X4 ∷ CK43 ∷ X4 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (Sb1-0-43-2 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  b2 = at 5 1 (CS02 ∷ []) (refl) ▸
       at 2 4 (CS02 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CK43 ∷ X4 ∷ CS02 ∷ []) (CS02 ∷ X4 ∷ CK43 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb1-0-2-3 ∷ []) (refl) ▸
       at 3 4 (Toff234 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK43 ∷ X4 ∷ Toff234 ∷ []) (Toff234 ∷ X4 ∷ CK43 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (CS02⁻ ∷ []) (refl) ▸
       at 4 4 (CS02⁻ ∷ X4 ∷ CK43 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CK43 ∷ X4 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ X4 ∷ CK43 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 0 5 (Sb1-0-43-2 ∷ []) (refl) ▸ done


-- F4 K3^0|CS12^1: 20 steps
lem-F4-K3ᵖ0∣CS12ᵖ1 : Complete 4 → ⟪ (X4 ∷ CK43 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3ᵖ0∣CS12ᵖ1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CK43 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Toff012 ∷ CCZ034 ∷ X4 ∷ CK43 ∷ Toff012 ∷ X4 ∷ CCZ034 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b0 = at 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 1 (Bx0-1243 ∷ []) (lem-sym23-at243243 c4) ▸
       at 3 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-beta-T-at3443 c4) ▸
       at 2 2 (Toff012 ∷ X4 ∷ []) (sym (c₃ (Toff) (X ↑))) ▸
       at 1 2 (Toff012 ∷ CK43 ∷ []) (sym (c₃ (Toff) (CK₁₀))) ▸
       at 0 2 (Toff012 ∷ X4 ∷ []) (sym (c₃ (Toff) (X ↑))) ▸
       at 1 4 (CCZ034 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CK43 ∷ X4 ∷ CCZ034 ∷ []) (CCZ034 ∷ X4 ∷ CK43 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff012 ∷ X4 ∷ []) (sym (c₃ (Toff) (X ↑))) ▸ done

  b1 : Chain (Toff012 ∷ CCZ034 ∷ X4 ∷ CK43 ∷ Toff012 ∷ X4 ∷ CCZ034 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ Toff324 ∷ X4 ∷ CK43 ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b1 = at 3 2 (Toff012 ∷ CK43 ∷ []) (sym (c₃ (Toff) (CK₁₀))) ▸
       at 2 2 (Toff012 ∷ X4 ∷ []) (sym (c₃ (Toff) (X ↑))) ▸
       at 3 4 (CCZ034 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CK43 ∷ X4 ∷ CCZ034 ∷ []) (CCZ034 ∷ X4 ∷ CK43 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx0-1243 ∷ []) (sym (lem-beta-T-at3443 c4)) ▸
       at 0 1 (Bx0-1423 ∷ []) (lem-sym23-at3443 c4) ▸
       at 1 4 (Toff324 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK43 ∷ X4 ∷ Toff324 ∷ []) (Toff324 ∷ X4 ∷ CK43 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS13 ∷ []) (refl) ▸
       at 7 1 (CS13⁻ ∷ []) (refl) ▸ done

  b2 : Chain (Bx0-1423 ∷ Toff324 ∷ X4 ∷ CK43 ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  b2 = at 2 6 (CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK43 ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CK43 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done


-- F4 K3^0|CS13^1: 24 steps
lem-F4-K3ᵖ0∣CS13ᵖ1 : Complete 4 → ⟪ (X4 ∷ CK43 ∷ X4 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-43-2 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3ᵖ0∣CS13ᵖ1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CK43 ∷ X4 ∷ Sb0-1-43-2 ∷ []) (Toff012 ∷ CCZ034 ∷ X4 ∷ CK43 ∷ X4 ∷ Toff012 ∷ CCZ034 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ [])
  b0 = at 3 1 (Bx0-1432 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 3 1 (Bx0-1423 ∷ []) (lem-sym34-at2442 c4) ▸
       at 3 1 (Bx0-1243 ∷ []) (lem-sym23-at243243 c4) ▸
       at 3 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-beta-T-at3443 c4) ▸
       at 2 2 (Toff012 ∷ X4 ∷ []) (sym (c₃ (Toff) (X ↑))) ▸
       at 1 2 (Toff012 ∷ CK43 ∷ []) (sym (c₃ (Toff) (CK₁₀))) ▸
       at 0 2 (Toff012 ∷ X4 ∷ []) (sym (c₃ (Toff) (X ↑))) ▸
       at 1 4 (CCZ034 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CK43 ∷ X4 ∷ CCZ034 ∷ []) (CCZ034 ∷ X4 ∷ CK43 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Toff012 ∷ CCZ034 ∷ X4 ∷ CK43 ∷ X4 ∷ Toff012 ∷ CCZ034 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ []) (Bx0-1432 ∷ Toff234 ∷ X4 ∷ CK43 ∷ X4 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ [])
  b1 = at 4 2 (Toff012 ∷ X4 ∷ []) (sym (c₃ (Toff) (X ↑))) ▸
       at 3 2 (Toff012 ∷ CK43 ∷ []) (sym (c₃ (Toff) (CK₁₀))) ▸
       at 2 2 (Toff012 ∷ X4 ∷ []) (sym (c₃ (Toff) (X ↑))) ▸
       at 3 4 (CCZ034 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CK43 ∷ X4 ∷ CCZ034 ∷ []) (CCZ034 ∷ X4 ∷ CK43 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx0-1243 ∷ []) (sym (lem-beta-T-at3443 c4)) ▸
       at 0 1 (Bx0-1423 ∷ []) (lem-sym23-at3443 c4) ▸
       at 0 1 (Bx0-1432 ∷ []) (lem-sym34-at243243 c4) ▸
       at 1 4 (Toff234 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK43 ∷ X4 ∷ Toff234 ∷ []) (Toff234 ∷ X4 ∷ CK43 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Bx0-1432 ∷ Toff234 ∷ X4 ∷ CK43 ∷ X4 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ []) (Sb0-1-43-2 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  b2 = at 5 1 (CS12 ∷ []) (refl) ▸
       at 2 4 (CS12 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK43 ∷ X4 ∷ CS12 ∷ []) (CS12 ∷ X4 ∷ CK43 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb0-1-2-3 ∷ []) (refl) ▸
       at 3 4 (Toff234 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK43 ∷ X4 ∷ Toff234 ∷ []) (Toff234 ∷ X4 ∷ CK43 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 4 4 (CS12⁻ ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK43 ∷ X4 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ X4 ∷ CK43 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-43-2 ∷ []) (refl) ▸ done


-- sym34 @122441: 5 steps
lem-sym34-at122441 : Complete 4 → ⟪ (Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ []) ⟫ʷ
lem-sym34-at122441 c4 = run b0
  where
  b0 : Chain (Bx0-2431 ∷ []) (Bx0-2413 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1432 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2431⟩ c4) ▸
       at 1 1 (Bx0-1423 ∷ []) (lem-sym34-at2442 c4) ▸
       at 0 2 (Bx0-2413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1423⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- beta-T @12213443: 8 steps
lem-beta-T-at12213443 : Complete 4 → ⟪ (Bx0-2143 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) ⟫ʷ
lem-beta-T-at12213443 c4 = run b0
  where
  b0 : Chain (Bx0-2143 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1243 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2143⟩ c4) ▸
       at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-beta-T-at3443 c4) ▸
       at 0 2 (Toff012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff012 ∷ []) (Toff012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 2 2 (Toff012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff012 ∷ []) (Toff012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 4 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- F4 K3^0|CS23^1: 24 steps
lem-F4-K3ᵖ0∣CS23ᵖ1 : Complete 4 → ⟪ (X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3ᵖ0∣CS23ᵖ1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Toff012 ∷ CCZ034 ∷ X4 ∷ CK43 ∷ X4 ∷ Toff012 ∷ CCZ034 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b0 = at 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 1 (Bx0-2413 ∷ []) (lem-sym34-at122441 c4) ▸
       at 3 1 (Bx0-2143 ∷ []) (lem-sym23-at12243143 c4) ▸
       at 3 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-beta-T-at12213443 c4) ▸
       at 2 2 (Toff012 ∷ X4 ∷ []) (sym (c₃ (Toff) (X ↑))) ▸
       at 1 2 (Toff012 ∷ CK43 ∷ []) (sym (c₃ (Toff) (CK₁₀))) ▸
       at 0 2 (Toff012 ∷ X4 ∷ []) (sym (c₃ (Toff) (X ↑))) ▸
       at 1 4 (CCZ034 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CK43 ∷ X4 ∷ CCZ034 ∷ []) (CCZ034 ∷ X4 ∷ CK43 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Toff012 ∷ CCZ034 ∷ X4 ∷ CK43 ∷ X4 ∷ Toff012 ∷ CCZ034 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ X4 ∷ CK43 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b1 = at 4 2 (Toff012 ∷ X4 ∷ []) (sym (c₃ (Toff) (X ↑))) ▸
       at 3 2 (Toff012 ∷ CK43 ∷ []) (sym (c₃ (Toff) (CK₁₀))) ▸
       at 2 2 (Toff012 ∷ X4 ∷ []) (sym (c₃ (Toff) (X ↑))) ▸
       at 3 4 (CCZ034 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CK43 ∷ X4 ∷ CCZ034 ∷ []) (CCZ034 ∷ X4 ∷ CK43 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx0-2143 ∷ []) (sym (lem-beta-T-at12213443 c4)) ▸
       at 0 1 (Bx0-2413 ∷ []) (lem-sym23-at12213443 c4) ▸
       at 0 1 (Bx0-2431 ∷ []) (lem-sym34-at12243143 c4) ▸
       at 1 4 (Toff134 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK43 ∷ X4 ∷ Toff134 ∷ []) (Toff134 ∷ X4 ∷ CK43 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Bx0-2431 ∷ Toff134 ∷ X4 ∷ CK43 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  b2 = at 5 1 (CS12 ∷ []) (refl) ▸
       at 2 4 (CS12 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK43 ∷ X4 ∷ CS12 ∷ []) (CS12 ∷ X4 ∷ CK43 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 3 4 (Toff134 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK43 ∷ X4 ∷ Toff134 ∷ []) (Toff134 ∷ X4 ∷ CK43 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 4 4 (CS12⁻ ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK43 ∷ X4 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ X4 ∷ CK43 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done


-- F4 CS01^0|iI^1: 30 steps
lem-F4-CS01ᵖ0∣iIᵖ1 : Complete 4 → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS01ᵖ0∣iIᵖ1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ []) (X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ S4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ [])
  b0 = at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 11 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 13 1 (CS03⁻ ∷ []) (refl) ▸
       at 12 4 (S4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS03⁻ ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 14 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸ done

  b1 : Chain (X4 ∷ Bx2-0413 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ S4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ []) (X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ CCZ123 ∷ X4 ∷ S4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ [])
  b1 = at 9 4 (S4 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff314 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (CS03 ∷ []) (refl) ▸
       at 6 4 (S4 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS03 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CS03 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 8 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 3 4 (S4 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff314 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (X4 ∷ Toff204 ∷ X4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff204 ∷ CCZ123 ∷ X4 ∷ S4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ []) (S4 ∷ X4 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ [])
  b2 = at 8 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 9 4 (S4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CCZ123 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 6 4 (S4 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ Toff204 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 4 (S4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CCZ123 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (S4 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ Toff204 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 4 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸ done

  b3 : Chain (S4 ∷ X4 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb2-0-3-1 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ []) (S4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b3 = at 2 4 (Bx2-0413 ∷ []) (sym (lem-beta-T-at0210243143 c4)) ▸
       at 3 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 4 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 [] (lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl) ▸
       at 2 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done


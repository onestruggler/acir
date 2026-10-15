{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D035 where

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
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-box-tQ-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-box-tQ-at243243)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CX04-CCZ123)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-comm-CX14-CCZ023)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-comm-CSd23-TOFF014)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-comm-CS13-TOFF204 ; lem-comm-CSd13-TOFF204)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-comm-CS23-TOFF014 ; lem-comm-SWAP14-BOX⟨2·03⟩)
open import Examples.Groups.Clifford+CS.Five.D.R016 using (lem-comm-SWAP24-BOX⟨0·13⟩)
-- CXbc-box @0210243143: 17 steps
lem-CXbc-box-at0210243143 : Complete 4 → ⟪ (CX41 ∷ Bx2-0413 ∷ CX41 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CCZ034 ∷ []) ⟫ʷ
lem-CXbc-box-at0210243143 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX41 ∷ Bx2-0413 ∷ CX41 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CX41 ∷ CCZ234 ∷ CS34 ∷ CX04 ∷ CS34⁻ ∷ CCZ123 ∷ CX04 ∷ CS03 ∷ CX41 ∷ [])
  b0 = at 1 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-box-tQ-at0210243143 c4) ▸
       at 0 2 (Toff204 ∷ CX41 ∷ []) (pw3 c4 (CX41 ∷ Toff204 ∷ []) (Toff204 ∷ CX41 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ123 ∷ CX41 ∷ CCZ234 ∷ []) (lw0 c4 (CX41 ∷ CCZ123 ∷ []) (CCZ123 ∷ CX41 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff204 ∷ CCZ234 ∷ CCZ034 ∷ []) (pw1 c4 (CCZ234 ∷ Toff204 ∷ []) (Toff204 ∷ CCZ234 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff204 ∷ CX41 ∷ []) (pw3 c4 (CX41 ∷ Toff204 ∷ []) (Toff204 ∷ CX41 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ []) (pw1 c4 (CCZ034 ∷ []) (CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ123 ∷ CS03 ∷ []) (lw4 c4 (CS03 ∷ CCZ123 ∷ []) (CCZ123 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ123 ∷ CX04 ∷ []) (lem-comm-CX04-CCZ123 c4) ▸ done

  b1 : Chain (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CX41 ∷ CCZ234 ∷ CS34 ∷ CX04 ∷ CS34⁻ ∷ CCZ123 ∷ CX04 ∷ CS03 ∷ CX41 ∷ []) (Bx2-0413 ∷ CX41 ∷ CCZ034 ∷ CX41 ∷ [])
  b1 = at 7 2 (CCZ123 ∷ CS34⁻ ∷ []) (lw0 c4 (CS34⁻ ∷ CCZ123 ∷ []) (CCZ123 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ123 ∷ CX04 ∷ []) (lem-comm-CX04-CCZ123 c4) ▸
       at 5 2 (CCZ123 ∷ CS34 ∷ []) (lw0 c4 (CS34 ∷ CCZ123 ∷ []) (CCZ123 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 6 5 (CCZ034 ∷ []) (pw1 c4 (CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ123 ∷ CCZ234 ∷ []) (lw0 c4 (CCZ234 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ123 ∷ CX41 ∷ CCZ234 ∷ []) (lw0 c4 (CX41 ∷ CCZ123 ∷ []) (CCZ123 ∷ CX41 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CX41 ∷ []) (lw0 c4 (CX41 ∷ CCZ234 ∷ CCZ234 ∷ []) (CX41 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx2-0413 ∷ []) (sym (lem-box-tQ-at0210243143 c4)) ▸ done

  b2 : Chain (Bx2-0413 ∷ CX41 ∷ CCZ034 ∷ CX41 ∷ []) (Bx2-0413 ∷ CCZ034 ∷ [])
  b2 = at 1 3 (CCZ034 ∷ []) (pw2 c4 (CX41 ∷ CCZ034 ∷ CX41 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸ done


-- CXcb-box @0210243143: 18 steps
lem-CXcb-box-at0210243143 : Complete 4 → ⟪ (CX14 ∷ Bx2-0413 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CCZ013 ∷ []) ⟫ʷ
lem-CXcb-box-at0210243143 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX14 ∷ Bx2-0413 ∷ CX14 ∷ []) (Toff204 ∷ CCZ123 ∷ CX14 ∷ Toff201 ∷ CS13 ∷ CX01 ∷ Toff204 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ CCZ123 ∷ CX14 ∷ [])
  b0 = at 1 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-box-tQ-at0210243143 c4) ▸
       at 0 2 (Toff204 ∷ CX14 ∷ Toff201 ∷ []) (pw3 c4 (CX14 ∷ Toff204 ∷ []) (Toff204 ∷ CX14 ∷ Toff201 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ123 ∷ Toff201 ∷ CCZ013 ∷ []) (lw4 c4 (Toff201 ∷ CCZ123 ∷ []) (CCZ123 ∷ Toff201 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ123 ∷ CX14 ∷ []) (lw0 c4 (CX14 ∷ CCZ123 ∷ []) (CCZ123 ∷ CX14 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) (lw4 c4 (CCZ013 ∷ []) (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Toff204 ∷ CS03 ∷ []) (pw1 c4 (CS03 ∷ Toff204 ∷ []) (Toff204 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff204 ∷ CX01 ∷ []) (pw3 c4 (CX01 ∷ Toff204 ∷ []) (Toff204 ∷ CX01 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff204 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-TOFF204 c4) ▸ done

  b1 : Chain (Toff204 ∷ CCZ123 ∷ CX14 ∷ Toff201 ∷ CS13 ∷ CX01 ∷ Toff204 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ CCZ123 ∷ CX14 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ CX14 ∷ CCZ013 ∷ CX14 ∷ [])
  b1 = at 5 2 (Toff204 ∷ CX01 ∷ []) (pw3 c4 (CX01 ∷ Toff204 ∷ []) (Toff204 ∷ CX01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff204 ∷ CS13 ∷ []) (lem-comm-CS13-TOFF204 c4) ▸
       at 5 5 (CCZ013 ∷ []) (lw4 c4 (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff204 ∷ Toff201 ∷ []) (pw3 c4 (Toff201 ∷ Toff204 ∷ []) (Toff204 ∷ Toff201 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff204 ∷ CX14 ∷ Toff201 ∷ []) (pw3 c4 (CX14 ∷ Toff204 ∷ []) (Toff204 ∷ CX14 ∷ Toff201 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CX14 ∷ []) (pw3 c4 (CX14 ∷ Toff201 ∷ Toff201 ∷ []) (CX14 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ123 ∷ CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ123 ∷ CX14 ∷ []) (lw0 c4 (CX14 ∷ CCZ123 ∷ []) (CCZ123 ∷ CX14 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ CX14 ∷ CCZ013 ∷ CX14 ∷ []) (Bx2-0413 ∷ CCZ013 ∷ [])
  b2 = at 0 4 (Bx2-0413 ∷ []) (sym (lem-box-tQ-at0210243143 c4)) ▸
       at 1 3 (CCZ013 ∷ []) (pw2 c4 (CX14 ∷ CCZ013 ∷ CX14 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸ done


-- SWbc-box @0210243143: 11 steps
lem-SWbc-box-at0210243143 : Complete 4 → ⟪ (Sw14 ∷ Bx2-0413 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ []) ⟫ʷ
lem-SWbc-box-at0210243143 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw14 ∷ Bx2-0413 ∷ Sw14 ∷ []) (CX41 ∷ Bx2-0413 ∷ CX41 ∷ CCZ034 ∷ CCZ013 ∷ CCZ034 ∷ CCZ013 ∷ CCZ034 ∷ [])
  b0 = at 0 1 (CX41 ∷ CX14 ∷ CX41 ∷ []) (lw0 c4 (Sw14 ∷ []) (CX41 ∷ CX14 ∷ CX41 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CX41 ∷ CX14 ∷ CX41 ∷ []) (lw0 c4 (Sw14 ∷ []) (CX41 ∷ CX14 ∷ CX41 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (Bx2-0413 ∷ CCZ034 ∷ []) (lem-CXbc-box-at0210243143 c4) ▸
       at 3 2 (CX14 ∷ CCZ013 ∷ CCZ034 ∷ []) (pw2 c4 (CCZ034 ∷ CX14 ∷ []) (CX14 ∷ CCZ013 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Bx2-0413 ∷ CCZ013 ∷ []) (lem-CXcb-box-at0210243143 c4) ▸
       at 4 2 (CX41 ∷ CCZ034 ∷ []) (pw2 c4 (CCZ034 ∷ CX41 ∷ []) (CX41 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CX41 ∷ CCZ034 ∷ CCZ013 ∷ []) (pw2 c4 (CCZ013 ∷ CX41 ∷ []) (CX41 ∷ CCZ034 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CX41 ∷ CCZ034 ∷ CCZ013 ∷ []) (pw2 c4 (CCZ013 ∷ CX41 ∷ []) (CX41 ∷ CCZ034 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CX41 ∷ Bx2-0413 ∷ CX41 ∷ CCZ034 ∷ CCZ013 ∷ CCZ034 ∷ CCZ013 ∷ CCZ034 ∷ []) (Bx2-0413 ∷ [])
  b1 = at 3 5 (CCZ034 ∷ []) (pw2 c4 (CCZ034 ∷ CCZ013 ∷ CCZ034 ∷ CCZ013 ∷ CCZ034 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Bx2-0413 ∷ CCZ034 ∷ []) (lem-CXbc-box-at0210243143 c4) ▸
       at 1 2 [] (pw1 c4 (CCZ034 ∷ CCZ034 ∷ []) [] tt tt Eq.refl) ▸ done


-- nat-SWbc @0210243143: 23 steps
lem-nat-SWbc-at0210243143 : Complete 4 → ⟪ (Sw14 ∷ Bx2-0413 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0143 ∷ []) ⟫ʷ
lem-nat-SWbc-at0210243143 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw14 ∷ Bx2-0413 ∷ Sw14 ∷ []) (CCZ012 ∷ Toff201 ∷ CCZ024 ∷ Toff024 ∷ Bx2-03 ∷ Toff024 ∷ Sw14 ∷ CCZ012 ∷ Bx2-03 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ Sw14 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw14 ∷ []) (pw3 c4 (Sw14 ∷ CCZ024 ∷ []) (CCZ012 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff201 ∷ Sw14 ∷ []) (pw3 c4 (Sw14 ∷ Toff204 ∷ []) (Toff201 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) (refl) ▸
       at 2 2 (CCZ024 ∷ Sw14 ∷ []) (pw3 c4 (Sw14 ∷ CCZ012 ∷ []) (CCZ024 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff024 ∷ Sw14 ∷ []) (pw3 c4 (Sw14 ∷ Toff012 ∷ []) (Toff024 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx2-03 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨2·03⟩ c4) ▸
       at 5 2 (Toff024 ∷ Sw14 ∷ []) (pw3 c4 (Sw14 ∷ Toff012 ∷ []) (Toff024 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ012 ∷ Toff201 ∷ CCZ024 ∷ Toff024 ∷ Bx2-03 ∷ Toff024 ∷ Sw14 ∷ CCZ012 ∷ Bx2-03 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ Sw14 ∷ []) (CCZ012 ∷ Toff201 ∷ CCZ024 ∷ Toff024 ∷ Bx2-03 ∷ Toff024 ∷ CCZ024 ∷ Bx2-03 ∷ Toff201 ∷ CCZ012 ∷ CCZ024 ∷ Toff024 ∷ Bx2-03 ∷ Sw14 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ Sw14 ∷ [])
  b1 = at 6 2 (CCZ024 ∷ Sw14 ∷ []) (pw3 c4 (Sw14 ∷ CCZ012 ∷ []) (CCZ024 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Bx2-03 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨2·03⟩ c4) ▸
       at 8 2 (Toff201 ∷ Sw14 ∷ []) (pw3 c4 (Sw14 ∷ Toff204 ∷ []) (Toff201 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ012 ∷ Sw14 ∷ []) (pw3 c4 (Sw14 ∷ CCZ024 ∷ []) (CCZ012 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 11 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) (refl) ▸
       at 10 2 (CCZ024 ∷ Sw14 ∷ []) (pw3 c4 (Sw14 ∷ CCZ012 ∷ []) (CCZ024 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (Toff024 ∷ Sw14 ∷ []) (pw3 c4 (Sw14 ∷ Toff012 ∷ []) (Toff024 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (Bx2-03 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨2·03⟩ c4) ▸ done

  b2 : Chain (CCZ012 ∷ Toff201 ∷ CCZ024 ∷ Toff024 ∷ Bx2-03 ∷ Toff024 ∷ CCZ024 ∷ Bx2-03 ∷ Toff201 ∷ CCZ012 ∷ CCZ024 ∷ Toff024 ∷ Bx2-03 ∷ Sw14 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ Sw14 ∷ []) (Bx2-0143 ∷ [])
  b2 = at 13 2 (Toff024 ∷ Sw14 ∷ []) (pw3 c4 (Sw14 ∷ Toff012 ∷ []) (Toff024 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (CCZ024 ∷ Sw14 ∷ []) (pw3 c4 (Sw14 ∷ CCZ012 ∷ []) (CCZ024 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 15 2 (Bx2-03 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨2·03⟩ c4) ▸
       at 16 2 [] (lw0 c4 (Sw14 ∷ Sw14 ∷ []) [] tt tt Eq.refl) ▸
       at 2 6 (Bx0-243 ∷ []) (refl) ▸
       at 5 6 (Bx0-243 ∷ []) (refl) ▸
       at 0 6 (Bx2-0143 ∷ []) (refl) ▸ done


-- sym-bc @0210243143: 2 steps
lem-sym-bc-at0210243143 : Complete 4 → ⟪ (Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0143 ∷ []) ⟫ʷ
lem-sym-bc-at0210243143 c4 = run b0
  where
  b0 : Chain (Bx2-0413 ∷ []) (Bx2-0143 ∷ [])
  b0 = at 0 1 (Sw14 ∷ Bx2-0413 ∷ Sw14 ∷ []) (sym (lem-SWbc-box-at0210243143 c4)) ▸
       at 0 3 (Bx2-0143 ∷ []) (lem-nat-SWbc-at0210243143 c4) ▸ done


-- box-perm-1324 @0210243143: 1 steps
lem-box-perm-1324-at0210243143 : Complete 4 → ⟪ (Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0143 ∷ []) ⟫ʷ
lem-box-perm-1324-at0210243143 c4 = run b0
  where
  b0 : Chain (Bx2-0413 ∷ []) (Bx2-0143 ∷ [])
  b0 = at 0 1 (Bx2-0143 ∷ []) (lem-sym-bc-at0210243143 c4) ▸ done


-- cQ @0210213443: 7 steps
lem-cQ-at0210213443 : Complete 4 → ⟪ (CCZ012 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ CCZ012 ∷ []) ⟫ʷ
lem-cQ-at0210213443 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ012 ∷ [])
  b0 = at 0 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ234 ∷ CS02 ∷ []) (pw1 c4 (CS02 ∷ CCZ234 ∷ []) (CCZ234 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ)) ▸
       at 2 2 (CCZ234 ∷ CS12⁻ ∷ []) (lw0 c4 (CS12⁻ ∷ CCZ234 ∷ []) (CCZ234 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ)) ▸
       at 0 2 (CCZ234 ∷ CS12 ∷ []) (lw0 c4 (CS12 ∷ CCZ234 ∷ []) (CCZ234 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 1 5 (CCZ012 ∷ []) (lw4 c4 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸ done


-- tP @0210213443: 7 steps
lem-tP-at0210213443 : Complete 4 → ⟪ (Toff201 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ Toff201 ∷ []) ⟫ʷ
lem-tP-at0210213443 c4 = run b0
  where
  b0 : Chain (Toff201 ∷ Toff234 ∷ []) (Toff234 ∷ Toff201 ∷ [])
  b0 = at 0 1 (K2 ∷ CCZ012 ∷ K2⁻ ∷ []) (lw4 c4 (Toff201 ∷ []) (K2 ∷ CCZ012 ∷ K2⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (K2 ∷ CCZ234 ∷ K2⁻ ∷ []) (lw0 c4 (Toff234 ∷ []) (K2 ∷ CCZ234 ∷ K2⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (K2⁻ ∷ K2 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 (CCZ234 ∷ CCZ012 ∷ []) (lem-cQ-at0210213443 c4) ▸
       at 2 0 (K2⁻ ∷ K2 ∷ []) (lw4 c4 [] (K2⁻ ∷ K2 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Toff234 ∷ []) (lw0 c4 (K2 ∷ CCZ234 ∷ K2⁻ ∷ []) (Toff234 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Toff201 ∷ []) (lw4 c4 (K2 ∷ CCZ012 ∷ K2⁻ ∷ []) (Toff201 ∷ []) tt tt Eq.refl) ▸ done


-- VPQ @0210213443: 14 steps
lem-VPQ-at0210213443 : Complete 4 → ⟪ (Toff201 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ []) ⟫ʷ
lem-VPQ-at0210213443 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff201 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ []) (CS34⁻ ∷ CS01⁻ ∷ S2 ∷ Toff234 ∷ Toff201 ∷ S2⁻ ∷ [])
  b0 = at 0 2 (CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ []) (lw4 c4 (Toff201 ∷ CCZ012 ∷ []) (CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS34⁻ ∷ S2 ∷ Toff234 ∷ S2⁻ ∷ []) (lw0 c4 (Toff234 ∷ CCZ234 ∷ []) (CS34⁻ ∷ S2 ∷ Toff234 ∷ S2⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS34⁻ ∷ S2⁻ ∷ []) (c₃ ((S • S • S) ↑ ↑) (CS • CS • CS)) ▸
       at 2 2 (CS34⁻ ∷ Toff201 ∷ []) (c₃ (Toffᵗ) (CS • CS • CS)) ▸
       at 1 2 (CS34⁻ ∷ S2 ∷ []) (c₃ (S ↑ ↑) (CS • CS • CS)) ▸
       at 0 2 (CS34⁻ ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) ((CS • CS • CS) ↑)) ▸
       at 4 2 [] (lw4 c4 (S2⁻ ∷ S2 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 (Toff234 ∷ Toff201 ∷ []) (lem-tP-at0210213443 c4) ▸ done

  b1 : Chain (CS34⁻ ∷ CS01⁻ ∷ S2 ∷ Toff234 ∷ Toff201 ∷ S2⁻ ∷ []) (Toff234 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ [])
  b1 = at 4 0 (S2⁻ ∷ S2 ∷ []) (lw4 c4 [] (S2⁻ ∷ S2 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (S2 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (S)) ▸
       at 2 2 (Toff234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (Toff)) ▸
       at 3 2 (S2⁻ ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (S • S • S)) ▸
       at 0 4 (Toff234 ∷ CCZ234 ∷ []) (lw0 c4 (CS34⁻ ∷ S2 ∷ Toff234 ∷ S2⁻ ∷ []) (Toff234 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff201 ∷ CCZ012 ∷ []) (lw4 c4 (CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ []) (Toff201 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸ done


-- QVQ @0210213443: 3 steps
lem-QVQ-at0210213443 : Complete 4 → ⟪ (CCZ234 ∷ Toff201 ∷ CCZ012 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ Toff201 ∷ CCZ012 ∷ Toff234 ∷ []) ⟫ʷ
lem-QVQ-at0210213443 c4 = run b0
  where
  b0 : Chain (CCZ234 ∷ Toff201 ∷ CCZ012 ∷ CCZ234 ∷ []) (Toff234 ∷ Toff201 ∷ CCZ012 ∷ Toff234 ∷ [])
  b0 = at 0 0 (Toff234 ∷ Toff234 ∷ []) (lw0 c4 [] (Toff234 ∷ Toff234 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (Toff201 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ []) (sym (lem-VPQ-at0210213443 c4)) ▸
       at 4 2 [] (lw0 c4 (CCZ234 ∷ CCZ234 ∷ []) [] tt tt Eq.refl) ▸ done


-- box-cP @0210213443: 12 steps
lem-box-cP-at0210213443 : Complete 4 → ⟪ (Bx2-0143 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ []) ⟫ʷ
lem-box-cP-at0210213443 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-0143 ∷ []) (CCZ012 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CZ03 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ Toff201 ∷ Bx0-243 ∷ Toff201 ∷ CCZ012 ∷ Bx0-243 ∷ []) (refl) ▸
       at 2 1 (CCZ024 ∷ Toff024 ∷ Bx2-03 ∷ Toff024 ∷ CCZ024 ∷ Bx2-03 ∷ []) (refl) ▸
       at 4 1 (CZ03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 2 6 (CCZ234 ∷ []) (pw1 c4 (CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CZ03 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ024 ∷ Toff024 ∷ Bx2-03 ∷ Toff024 ∷ CCZ024 ∷ Bx2-03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 10 1 (CZ03 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ012 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CZ03 ∷ []) (CCZ012 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ [])
  b1 = at 5 6 (CCZ234 ∷ []) (pw1 c4 (CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CZ03 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff234 ∷ Toff201 ∷ CCZ012 ∷ Toff234 ∷ []) (lem-QVQ-at0210213443 c4) ▸
       at 1 2 (Toff234 ∷ Toff201 ∷ []) (lem-tP-at0210213443 c4) ▸
       at 2 2 [] (lw4 c4 (Toff201 ∷ Toff201 ∷ []) [] tt tt Eq.refl) ▸ done


-- F4-K3-CS0: 19 steps
lem-F4-K3-CS0 : Complete 4 → ⟪ (X4 ∷ CK43 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3-CS0 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CK43 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (CCZ012 ∷ X4 ∷ CK43 ∷ X4 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b0 = at 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 5 1 (CS03 ∷ []) (refl) ▸
       at 7 1 (CS03⁻ ∷ []) (refl) ▸
       at 3 1 (Bx2-0143 ∷ []) (lem-box-perm-1324-at0210243143 c4) ▸
       at 3 1 (CCZ012 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ []) (lem-box-cP-at0210213443 c4) ▸
       at 2 2 (CCZ012 ∷ X4 ∷ []) (sym (c₃ (CCZ) (X ↑))) ▸
       at 1 2 (CCZ012 ∷ CK43 ∷ []) (sym (c₃ (CCZ) (CK₁₀))) ▸
       at 0 2 (CCZ012 ∷ X4 ∷ []) (sym (c₃ (CCZ) (X ↑))) ▸ done

  b1 : Chain (CCZ012 ∷ X4 ∷ CK43 ∷ X4 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  b1 = at 1 4 (Toff234 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK43 ∷ X4 ∷ Toff234 ∷ []) (Toff234 ∷ X4 ∷ CK43 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ012 ∷ X4 ∷ []) (sym (c₃ (CCZ) (X ↑))) ▸
       at 3 2 (CCZ012 ∷ CK43 ∷ []) (sym (c₃ (CCZ) (CK₁₀))) ▸
       at 2 2 (CCZ012 ∷ X4 ∷ []) (sym (c₃ (CCZ) (X ↑))) ▸
       at 3 4 (Toff234 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK43 ∷ X4 ∷ Toff234 ∷ []) (Toff234 ∷ X4 ∷ CK43 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx2-0143 ∷ []) (sym (lem-box-cP-at0210213443 c4)) ▸
       at 0 1 (Bx2-0413 ∷ []) (sym (lem-box-perm-1324-at0210243143 c4)) ▸
       at 1 7 (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CK43 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CK43 ∷ X4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CK43 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CK43 ∷ X4 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  b2 = at 2 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done


-- CXbc-box @243243: 17 steps
lem-CXbc-box-at243243 : Complete 4 → ⟪ (CX42 ∷ Bx0-1423 ∷ CX42 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CXbc-box-at243243 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX42 ∷ Bx0-1423 ∷ CX42 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CX42 ∷ CCZ034 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CCZ023 ∷ CX14 ∷ CS13 ∷ CX42 ∷ [])
  b0 = at 1 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-box-tQ-at243243 c4) ▸
       at 0 2 (Toff014 ∷ CX42 ∷ []) (pw3 c4 (CX42 ∷ Toff014 ∷ []) (Toff014 ∷ CX42 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ023 ∷ CX42 ∷ CCZ034 ∷ []) (pw1 c4 (CX42 ∷ CCZ023 ∷ []) (CCZ023 ∷ CX42 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff014 ∷ CCZ034 ∷ CCZ134 ∷ []) (pw2 c4 (CCZ034 ∷ Toff014 ∷ []) (Toff014 ∷ CCZ034 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff014 ∷ CX42 ∷ []) (pw3 c4 (CX42 ∷ Toff014 ∷ []) (Toff014 ∷ CX42 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ []) (lw0 c4 (CCZ134 ∷ []) (CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ023 ∷ CS13 ∷ []) (lw4 c4 (CS13 ∷ CCZ023 ∷ []) (CCZ023 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ023 ∷ CX14 ∷ []) (lem-comm-CX14-CCZ023 c4) ▸ done

  b1 : Chain (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CX42 ∷ CCZ034 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CCZ023 ∷ CX14 ∷ CS13 ∷ CX42 ∷ []) (Bx0-1423 ∷ CX42 ∷ CCZ134 ∷ CX42 ∷ [])
  b1 = at 7 2 (CCZ023 ∷ CS34⁻ ∷ []) (pw1 c4 (CS34⁻ ∷ CCZ023 ∷ []) (CCZ023 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ023 ∷ CX14 ∷ []) (lem-comm-CX14-CCZ023 c4) ▸
       at 5 2 (CCZ023 ∷ CS34 ∷ []) (pw1 c4 (CS34 ∷ CCZ023 ∷ []) (CCZ023 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 6 5 (CCZ134 ∷ []) (lw0 c4 (CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ023 ∷ CCZ034 ∷ []) (pw1 c4 (CCZ034 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ023 ∷ CX42 ∷ CCZ034 ∷ []) (pw1 c4 (CX42 ∷ CCZ023 ∷ []) (CCZ023 ∷ CX42 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CX42 ∷ []) (pw1 c4 (CX42 ∷ CCZ034 ∷ CCZ034 ∷ []) (CX42 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx0-1423 ∷ []) (sym (lem-box-tQ-at243243 c4)) ▸ done

  b2 : Chain (Bx0-1423 ∷ CX42 ∷ CCZ134 ∷ CX42 ∷ []) (Bx0-1423 ∷ CCZ134 ∷ [])
  b2 = at 1 3 (CCZ134 ∷ []) (lw0 c4 (CX42 ∷ CCZ134 ∷ CX42 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸ done


-- CXcb-box @243243: 18 steps
lem-CXcb-box-at243243 : Complete 4 → ⟪ (CX24 ∷ Bx0-1423 ∷ CX24 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CXcb-box-at243243 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX24 ∷ Bx0-1423 ∷ CX24 ∷ []) (Toff014 ∷ CCZ023 ∷ CX24 ∷ Toff012 ∷ CS23 ∷ CX12 ∷ Toff014 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CCZ023 ∷ CX24 ∷ [])
  b0 = at 1 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-box-tQ-at243243 c4) ▸
       at 0 2 (Toff014 ∷ CX24 ∷ Toff012 ∷ []) (pw3 c4 (CX24 ∷ Toff014 ∷ []) (Toff014 ∷ CX24 ∷ Toff012 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ023 ∷ Toff012 ∷ CCZ123 ∷ []) (lw4 c4 (Toff012 ∷ CCZ023 ∷ []) (CCZ023 ∷ Toff012 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ023 ∷ CX24 ∷ []) (pw1 c4 (CX24 ∷ CCZ023 ∷ []) (CCZ023 ∷ CX24 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Toff014 ∷ CS13 ∷ []) (pw2 c4 (CS13 ∷ Toff014 ∷ []) (Toff014 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff014 ∷ CX12 ∷ []) (pw3 c4 (CX12 ∷ Toff014 ∷ []) (Toff014 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-TOFF014 c4) ▸ done

  b1 : Chain (Toff014 ∷ CCZ023 ∷ CX24 ∷ Toff012 ∷ CS23 ∷ CX12 ∷ Toff014 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CCZ023 ∷ CX24 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ CX24 ∷ CCZ123 ∷ CX24 ∷ [])
  b1 = at 5 2 (Toff014 ∷ CX12 ∷ []) (pw3 c4 (CX12 ∷ Toff014 ∷ []) (Toff014 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff014 ∷ CS23 ∷ []) (lem-comm-CS23-TOFF014 c4) ▸
       at 5 5 (CCZ123 ∷ []) (lw4 c4 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff014 ∷ Toff012 ∷ []) (pw3 c4 (Toff012 ∷ Toff014 ∷ []) (Toff014 ∷ Toff012 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff014 ∷ CX24 ∷ Toff012 ∷ []) (pw3 c4 (CX24 ∷ Toff014 ∷ []) (Toff014 ∷ CX24 ∷ Toff012 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CX24 ∷ []) (pw3 c4 (CX24 ∷ Toff012 ∷ Toff012 ∷ []) (CX24 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ023 ∷ CCZ123 ∷ []) (lw4 c4 (CCZ123 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ023 ∷ CX24 ∷ []) (pw1 c4 (CX24 ∷ CCZ023 ∷ []) (CCZ023 ∷ CX24 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ CX24 ∷ CCZ123 ∷ CX24 ∷ []) (Bx0-1423 ∷ CCZ123 ∷ [])
  b2 = at 0 4 (Bx0-1423 ∷ []) (sym (lem-box-tQ-at243243 c4)) ▸
       at 1 3 (CCZ123 ∷ []) (lw0 c4 (CX24 ∷ CCZ123 ∷ CX24 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸ done


-- SWbc-box @243243: 11 steps
lem-SWbc-box-at243243 : Complete 4 → ⟪ (Sw24 ∷ Bx0-1423 ∷ Sw24 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ []) ⟫ʷ
lem-SWbc-box-at243243 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw24 ∷ Bx0-1423 ∷ Sw24 ∷ []) (CX42 ∷ Bx0-1423 ∷ CX42 ∷ CCZ134 ∷ CCZ123 ∷ CCZ134 ∷ CCZ123 ∷ CCZ134 ∷ [])
  b0 = at 0 1 (CX42 ∷ CX24 ∷ CX42 ∷ []) (lw0 c4 (Sw24 ∷ []) (CX42 ∷ CX24 ∷ CX42 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CX42 ∷ CX24 ∷ CX42 ∷ []) (lw0 c4 (Sw24 ∷ []) (CX42 ∷ CX24 ∷ CX42 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (Bx0-1423 ∷ CCZ134 ∷ []) (lem-CXbc-box-at243243 c4) ▸
       at 3 2 (CX24 ∷ CCZ123 ∷ CCZ134 ∷ []) (lw0 c4 (CCZ134 ∷ CX24 ∷ []) (CX24 ∷ CCZ123 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Bx0-1423 ∷ CCZ123 ∷ []) (lem-CXcb-box-at243243 c4) ▸
       at 4 2 (CX42 ∷ CCZ134 ∷ []) (lw0 c4 (CCZ134 ∷ CX42 ∷ []) (CX42 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CX42 ∷ CCZ134 ∷ CCZ123 ∷ []) (lw0 c4 (CCZ123 ∷ CX42 ∷ []) (CX42 ∷ CCZ134 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CX42 ∷ CCZ134 ∷ CCZ123 ∷ []) (lw0 c4 (CCZ123 ∷ CX42 ∷ []) (CX42 ∷ CCZ134 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CX42 ∷ Bx0-1423 ∷ CX42 ∷ CCZ134 ∷ CCZ123 ∷ CCZ134 ∷ CCZ123 ∷ CCZ134 ∷ []) (Bx0-1423 ∷ [])
  b1 = at 3 5 (CCZ134 ∷ []) (lw0 c4 (CCZ134 ∷ CCZ123 ∷ CCZ134 ∷ CCZ123 ∷ CCZ134 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Bx0-1423 ∷ CCZ134 ∷ []) (lem-CXbc-box-at243243 c4) ▸
       at 1 2 [] (lw0 c4 (CCZ134 ∷ CCZ134 ∷ []) [] tt tt Eq.refl) ▸ done


-- nat-SWbc @243243: 23 steps
lem-nat-SWbc-at243243 : Complete 4 → ⟪ (Sw24 ∷ Bx0-1423 ∷ Sw24 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ []) ⟫ʷ
lem-nat-SWbc-at243243 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw24 ∷ Bx0-1423 ∷ Sw24 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ014 ∷ Toff104 ∷ Bx0-13 ∷ Toff104 ∷ Sw24 ∷ CCZ012 ∷ Bx0-13 ∷ Toff014 ∷ CCZ014 ∷ Bx1-023 ∷ Sw24 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff014 ∷ Bx1-023 ∷ Toff014 ∷ CCZ014 ∷ Bx1-023 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw24 ∷ []) (pw3 c4 (Sw24 ∷ CCZ014 ∷ []) (CCZ012 ∷ Sw24 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff012 ∷ Sw24 ∷ []) (pw3 c4 (Sw24 ∷ Toff014 ∷ []) (Toff012 ∷ Sw24 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ []) (refl) ▸
       at 2 2 (CCZ014 ∷ Sw24 ∷ []) (pw3 c4 (Sw24 ∷ CCZ012 ∷ []) (CCZ014 ∷ Sw24 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff104 ∷ Sw24 ∷ []) (pw3 c4 (Sw24 ∷ Toff102 ∷ []) (Toff104 ∷ Sw24 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx0-13 ∷ Sw24 ∷ []) (lem-comm-SWAP24-BOX⟨0·13⟩ c4) ▸
       at 5 2 (Toff104 ∷ Sw24 ∷ []) (pw3 c4 (Sw24 ∷ Toff102 ∷ []) (Toff104 ∷ Sw24 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ012 ∷ Toff012 ∷ CCZ014 ∷ Toff104 ∷ Bx0-13 ∷ Toff104 ∷ Sw24 ∷ CCZ012 ∷ Bx0-13 ∷ Toff014 ∷ CCZ014 ∷ Bx1-023 ∷ Sw24 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ014 ∷ Toff104 ∷ Bx0-13 ∷ Toff104 ∷ CCZ014 ∷ Bx0-13 ∷ Toff012 ∷ CCZ012 ∷ CCZ014 ∷ Toff104 ∷ Bx0-13 ∷ Sw24 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ Sw24 ∷ [])
  b1 = at 6 2 (CCZ014 ∷ Sw24 ∷ []) (pw3 c4 (Sw24 ∷ CCZ012 ∷ []) (CCZ014 ∷ Sw24 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Bx0-13 ∷ Sw24 ∷ []) (lem-comm-SWAP24-BOX⟨0·13⟩ c4) ▸
       at 8 2 (Toff012 ∷ Sw24 ∷ []) (pw3 c4 (Sw24 ∷ Toff014 ∷ []) (Toff012 ∷ Sw24 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ012 ∷ Sw24 ∷ []) (pw3 c4 (Sw24 ∷ CCZ014 ∷ []) (CCZ012 ∷ Sw24 ∷ []) tt tt Eq.refl) ▸
       at 11 1 (CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ []) (refl) ▸
       at 10 2 (CCZ014 ∷ Sw24 ∷ []) (pw3 c4 (Sw24 ∷ CCZ012 ∷ []) (CCZ014 ∷ Sw24 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (Toff104 ∷ Sw24 ∷ []) (pw3 c4 (Sw24 ∷ Toff102 ∷ []) (Toff104 ∷ Sw24 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (Bx0-13 ∷ Sw24 ∷ []) (lem-comm-SWAP24-BOX⟨0·13⟩ c4) ▸ done

  b2 : Chain (CCZ012 ∷ Toff012 ∷ CCZ014 ∷ Toff104 ∷ Bx0-13 ∷ Toff104 ∷ CCZ014 ∷ Bx0-13 ∷ Toff012 ∷ CCZ012 ∷ CCZ014 ∷ Toff104 ∷ Bx0-13 ∷ Sw24 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ Sw24 ∷ []) (Bx0-1243 ∷ [])
  b2 = at 13 2 (Toff104 ∷ Sw24 ∷ []) (pw3 c4 (Sw24 ∷ Toff102 ∷ []) (Toff104 ∷ Sw24 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (CCZ014 ∷ Sw24 ∷ []) (pw3 c4 (Sw24 ∷ CCZ012 ∷ []) (CCZ014 ∷ Sw24 ∷ []) tt tt Eq.refl) ▸
       at 15 2 (Bx0-13 ∷ Sw24 ∷ []) (lem-comm-SWAP24-BOX⟨0·13⟩ c4) ▸
       at 16 2 [] (lw0 c4 (Sw24 ∷ Sw24 ∷ []) [] tt tt Eq.refl) ▸
       at 2 6 (Bx1-043 ∷ []) (refl) ▸
       at 5 6 (Bx1-043 ∷ []) (refl) ▸
       at 0 6 (Bx0-1243 ∷ []) (refl) ▸ done


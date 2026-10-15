{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D015 where

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
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-box-tQ-at1221)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-box-tQ-at13243241 ; lem-cQ-at13243241)
open import Examples.Groups.Clifford+CS.Five.D.D011 using (lem-box-perm-2341)
open import Examples.Groups.Clifford+CS.Five.D.D014 using (lem-box-cP-at0110 ; lem-box-tQ-at12233441 ; lem-cQ-at133441 ; lem-sym-ab-at12233441)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CZ12-TOFF034)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CX13-CCZ024)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-comm-CSd14-TOFF023 ; lem-comm-CX23-CCZ014)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-comm-CZ23-CCZ014)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-comm-SWAP24-BOX⟨0·31⟩)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-comm-CX32-CCZ014 ; lem-comm-TOFF034-CSd12)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-comm-CS14-TOFF023 ; lem-comm-CX02-TOFF134)
-- box-tQ @133441: 13 steps
lem-box-tQ-at133441 : Complete 4 → ⟪ (Bx0-3241 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) ⟫ʷ
lem-box-tQ-at133441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-3241 ∷ []) (CCZ023 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ CCZ034 ∷ Toff304 ∷ CZ13 ∷ Toff304 ∷ CCZ034 ∷ CZ13 ∷ [])
  b0 = at 0 1 (CCZ023 ∷ Toff023 ∷ Bx3-041 ∷ Toff023 ∷ CCZ023 ∷ Bx3-041 ∷ []) (refl) ▸
       at 2 1 (CCZ034 ∷ Toff304 ∷ Bx0-31 ∷ Toff304 ∷ CCZ034 ∷ Bx0-31 ∷ []) (refl) ▸
       at 4 1 (CZ13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 2 6 (CCZ014 ∷ []) (pw2 c4 (CCZ034 ∷ Toff304 ∷ CZ13 ∷ Toff304 ∷ CCZ034 ∷ CZ13 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ034 ∷ Toff304 ∷ Bx0-31 ∷ Toff304 ∷ CCZ034 ∷ Bx0-31 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 10 1 (CZ13 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ023 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ CCZ034 ∷ Toff304 ∷ CZ13 ∷ Toff304 ∷ CCZ034 ∷ CZ13 ∷ []) (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ [])
  b1 = at 5 6 (CCZ014 ∷ []) (pw2 c4 (CCZ034 ∷ Toff304 ∷ CZ13 ∷ Toff304 ∷ CCZ034 ∷ CZ13 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Toff023 ∷ CCZ023 ∷ CZ23 ∷ []) (lw4 c4 (CCZ023 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ023 ∷ CZ23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ014 ∷ CZ23 ∷ []) (lem-comm-CZ23-CCZ014 c4) ▸
       at 1 2 (CCZ014 ∷ CCZ023 ∷ []) (lem-cQ-at133441 c4) ▸
       at 2 4 (Toff023 ∷ []) (lw4 c4 (CCZ023 ∷ CZ23 ∷ Toff023 ∷ CCZ023 ∷ []) (Toff023 ∷ []) tt tt Eq.refl) ▸ done


-- CXbc-box @133441: 17 steps
lem-CXbc-box-at133441 : Complete 4 → ⟪ (CX24 ∷ Bx0-3241 ∷ CX24 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3241 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CXbc-box-at133441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX24 ∷ Bx0-3241 ∷ CX24 ∷ []) (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CX24 ∷ CCZ012 ∷ CS12 ∷ CX32 ∷ CS12⁻ ∷ CCZ014 ∷ CX32 ∷ CS13 ∷ CX24 ∷ [])
  b0 = at 1 1 (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) (lem-box-tQ-at133441 c4) ▸
       at 0 2 (Toff023 ∷ CX24 ∷ []) (pw1 c4 (CX24 ∷ Toff023 ∷ []) (Toff023 ∷ CX24 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ014 ∷ CX24 ∷ CCZ012 ∷ []) (pw3 c4 (CX24 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX24 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff023 ∷ CCZ012 ∷ CCZ123 ∷ []) (lw4 c4 (CCZ012 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ012 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff023 ∷ CX24 ∷ []) (pw1 c4 (CX24 ∷ Toff023 ∷ []) (Toff023 ∷ CX24 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CS13 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ014 ∷ CS13 ∷ []) (pw2 c4 (CS13 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 c4) ▸ done

  b1 : Chain (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CX24 ∷ CCZ012 ∷ CS12 ∷ CX32 ∷ CS12⁻ ∷ CCZ014 ∷ CX32 ∷ CS13 ∷ CX24 ∷ []) (Bx0-3241 ∷ CX24 ∷ CCZ123 ∷ CX24 ∷ [])
  b1 = at 7 2 (CCZ014 ∷ CS12⁻ ∷ []) (pw3 c4 (CS12⁻ ∷ CCZ014 ∷ []) (CCZ014 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 c4) ▸
       at 5 2 (CCZ014 ∷ CS12 ∷ []) (pw3 c4 (CS12 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 6 5 (CCZ123 ∷ []) (lw4 c4 (CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CS13 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ014 ∷ CCZ012 ∷ []) (pw3 c4 (CCZ012 ∷ CCZ014 ∷ []) (CCZ014 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ014 ∷ CX24 ∷ CCZ012 ∷ []) (pw3 c4 (CX24 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX24 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CX24 ∷ []) (pw3 c4 (CX24 ∷ CCZ012 ∷ CCZ012 ∷ []) (CX24 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx0-3241 ∷ []) (sym (lem-box-tQ-at133441 c4)) ▸ done

  b2 : Chain (Bx0-3241 ∷ CX24 ∷ CCZ123 ∷ CX24 ∷ []) (Bx0-3241 ∷ CCZ123 ∷ [])
  b2 = at 1 3 (CCZ123 ∷ []) (lw0 c4 (CX24 ∷ CCZ123 ∷ CX24 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸ done


-- CXcb-box @133441: 18 steps
lem-CXcb-box-at133441 : Complete 4 → ⟪ (CX42 ∷ Bx0-3241 ∷ CX42 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3241 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CXcb-box-at133441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX42 ∷ Bx0-3241 ∷ CX42 ∷ []) (Toff023 ∷ CCZ014 ∷ CX42 ∷ Toff034 ∷ CS14 ∷ CX34 ∷ Toff023 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ CCZ014 ∷ CX42 ∷ [])
  b0 = at 1 1 (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) (lem-box-tQ-at133441 c4) ▸
       at 0 2 (Toff023 ∷ CX42 ∷ Toff034 ∷ []) (pw1 c4 (CX42 ∷ Toff023 ∷ []) (Toff023 ∷ CX42 ∷ Toff034 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ014 ∷ Toff034 ∷ CCZ134 ∷ []) (pw2 c4 (Toff034 ∷ CCZ014 ∷ []) (CCZ014 ∷ Toff034 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ014 ∷ CX42 ∷ []) (pw3 c4 (CX42 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX42 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) (lw0 c4 (CCZ134 ∷ []) (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Toff023 ∷ CS13 ∷ []) (lw4 c4 (CS13 ∷ Toff023 ∷ []) (Toff023 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff023 ∷ CX34 ∷ []) (pw1 c4 (CX34 ∷ Toff023 ∷ []) (Toff023 ∷ CX34 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff023 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-TOFF023 c4) ▸ done

  b1 : Chain (Toff023 ∷ CCZ014 ∷ CX42 ∷ Toff034 ∷ CS14 ∷ CX34 ∷ Toff023 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ CCZ014 ∷ CX42 ∷ []) (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CX42 ∷ CCZ134 ∷ CX42 ∷ [])
  b1 = at 5 2 (Toff023 ∷ CX34 ∷ []) (pw1 c4 (CX34 ∷ Toff023 ∷ []) (Toff023 ∷ CX34 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff023 ∷ CS14 ∷ []) (lem-comm-CS14-TOFF023 c4) ▸
       at 5 5 (CCZ134 ∷ []) (lw0 c4 (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff023 ∷ Toff034 ∷ []) (pw1 c4 (Toff034 ∷ Toff023 ∷ []) (Toff023 ∷ Toff034 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff023 ∷ CX42 ∷ Toff034 ∷ []) (pw1 c4 (CX42 ∷ Toff023 ∷ []) (Toff023 ∷ CX42 ∷ Toff034 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CX42 ∷ []) (pw1 c4 (CX42 ∷ Toff034 ∷ Toff034 ∷ []) (CX42 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ014 ∷ CCZ134 ∷ []) (pw2 c4 (CCZ134 ∷ CCZ014 ∷ []) (CCZ014 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ014 ∷ CX42 ∷ []) (pw3 c4 (CX42 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX42 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CX42 ∷ CCZ134 ∷ CX42 ∷ []) (Bx0-3241 ∷ CCZ134 ∷ [])
  b2 = at 0 4 (Bx0-3241 ∷ []) (sym (lem-box-tQ-at133441 c4)) ▸
       at 1 3 (CCZ134 ∷ []) (lw0 c4 (CX42 ∷ CCZ134 ∷ CX42 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸ done


-- SWbc-box @133441: 11 steps
lem-SWbc-box-at133441 : Complete 4 → ⟪ (Sw24 ∷ Bx0-3241 ∷ Sw24 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3241 ∷ []) ⟫ʷ
lem-SWbc-box-at133441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw24 ∷ Bx0-3241 ∷ Sw24 ∷ []) (CX24 ∷ Bx0-3241 ∷ CX24 ∷ CCZ123 ∷ CCZ134 ∷ CCZ123 ∷ CCZ134 ∷ CCZ123 ∷ [])
  b0 = at 0 1 (CX24 ∷ CX42 ∷ CX24 ∷ []) (lw0 c4 (Sw24 ∷ []) (CX24 ∷ CX42 ∷ CX24 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CX24 ∷ CX42 ∷ CX24 ∷ []) (lw0 c4 (Sw24 ∷ []) (CX24 ∷ CX42 ∷ CX24 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (Bx0-3241 ∷ CCZ123 ∷ []) (lem-CXbc-box-at133441 c4) ▸
       at 3 2 (CX42 ∷ CCZ134 ∷ CCZ123 ∷ []) (lw0 c4 (CCZ123 ∷ CX42 ∷ []) (CX42 ∷ CCZ134 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Bx0-3241 ∷ CCZ134 ∷ []) (lem-CXcb-box-at133441 c4) ▸
       at 4 2 (CX24 ∷ CCZ123 ∷ []) (lw0 c4 (CCZ123 ∷ CX24 ∷ []) (CX24 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CX24 ∷ CCZ123 ∷ CCZ134 ∷ []) (lw0 c4 (CCZ134 ∷ CX24 ∷ []) (CX24 ∷ CCZ123 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CX24 ∷ CCZ123 ∷ CCZ134 ∷ []) (lw0 c4 (CCZ134 ∷ CX24 ∷ []) (CX24 ∷ CCZ123 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CX24 ∷ Bx0-3241 ∷ CX24 ∷ CCZ123 ∷ CCZ134 ∷ CCZ123 ∷ CCZ134 ∷ CCZ123 ∷ []) (Bx0-3241 ∷ [])
  b1 = at 3 5 (CCZ123 ∷ []) (lw0 c4 (CCZ123 ∷ CCZ134 ∷ CCZ123 ∷ CCZ134 ∷ CCZ123 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Bx0-3241 ∷ CCZ123 ∷ []) (lem-CXbc-box-at133441 c4) ▸
       at 1 2 [] (lw4 c4 (CCZ123 ∷ CCZ123 ∷ []) [] tt tt Eq.refl) ▸ done


-- nat-SWbc @133441: 23 steps
lem-nat-SWbc-at133441 : Complete 4 → ⟪ (Sw24 ∷ Bx0-3241 ∷ Sw24 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3421 ∷ []) ⟫ʷ
lem-nat-SWbc-at133441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw24 ∷ Bx0-3241 ∷ Sw24 ∷ []) (CCZ034 ∷ Toff034 ∷ CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Toff302 ∷ Sw24 ∷ CCZ034 ∷ Bx0-31 ∷ Toff023 ∷ CCZ023 ∷ Bx3-041 ∷ Sw24 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff023 ∷ Bx3-041 ∷ Toff023 ∷ CCZ023 ∷ Bx3-041 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw24 ∷ []) (pw1 c4 (Sw24 ∷ CCZ023 ∷ []) (CCZ034 ∷ Sw24 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff034 ∷ Sw24 ∷ []) (pw1 c4 (Sw24 ∷ Toff023 ∷ []) (Toff034 ∷ Sw24 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CCZ034 ∷ Toff304 ∷ Bx0-31 ∷ Toff304 ∷ CCZ034 ∷ Bx0-31 ∷ []) (refl) ▸
       at 2 2 (CCZ023 ∷ Sw24 ∷ []) (pw1 c4 (Sw24 ∷ CCZ034 ∷ []) (CCZ023 ∷ Sw24 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff302 ∷ Sw24 ∷ []) (pw1 c4 (Sw24 ∷ Toff304 ∷ []) (Toff302 ∷ Sw24 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx0-31 ∷ Sw24 ∷ []) (lem-comm-SWAP24-BOX⟨0·31⟩ c4) ▸
       at 5 2 (Toff302 ∷ Sw24 ∷ []) (pw1 c4 (Sw24 ∷ Toff304 ∷ []) (Toff302 ∷ Sw24 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff034 ∷ CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Toff302 ∷ Sw24 ∷ CCZ034 ∷ Bx0-31 ∷ Toff023 ∷ CCZ023 ∷ Bx3-041 ∷ Sw24 ∷ []) (CCZ034 ∷ Toff034 ∷ CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Toff302 ∷ CCZ023 ∷ Bx0-31 ∷ Toff034 ∷ CCZ034 ∷ CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Sw24 ∷ Toff304 ∷ CCZ034 ∷ Bx0-31 ∷ Sw24 ∷ [])
  b1 = at 6 2 (CCZ023 ∷ Sw24 ∷ []) (pw1 c4 (Sw24 ∷ CCZ034 ∷ []) (CCZ023 ∷ Sw24 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Bx0-31 ∷ Sw24 ∷ []) (lem-comm-SWAP24-BOX⟨0·31⟩ c4) ▸
       at 8 2 (Toff034 ∷ Sw24 ∷ []) (pw1 c4 (Sw24 ∷ Toff023 ∷ []) (Toff034 ∷ Sw24 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ034 ∷ Sw24 ∷ []) (pw1 c4 (Sw24 ∷ CCZ023 ∷ []) (CCZ034 ∷ Sw24 ∷ []) tt tt Eq.refl) ▸
       at 11 1 (CCZ034 ∷ Toff304 ∷ Bx0-31 ∷ Toff304 ∷ CCZ034 ∷ Bx0-31 ∷ []) (refl) ▸
       at 10 2 (CCZ023 ∷ Sw24 ∷ []) (pw1 c4 (Sw24 ∷ CCZ034 ∷ []) (CCZ023 ∷ Sw24 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (Toff302 ∷ Sw24 ∷ []) (pw1 c4 (Sw24 ∷ Toff304 ∷ []) (Toff302 ∷ Sw24 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (Bx0-31 ∷ Sw24 ∷ []) (lem-comm-SWAP24-BOX⟨0·31⟩ c4) ▸ done

  b2 : Chain (CCZ034 ∷ Toff034 ∷ CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Toff302 ∷ CCZ023 ∷ Bx0-31 ∷ Toff034 ∷ CCZ034 ∷ CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Sw24 ∷ Toff304 ∷ CCZ034 ∷ Bx0-31 ∷ Sw24 ∷ []) (Bx0-3421 ∷ [])
  b2 = at 13 2 (Toff302 ∷ Sw24 ∷ []) (pw1 c4 (Sw24 ∷ Toff304 ∷ []) (Toff302 ∷ Sw24 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (CCZ023 ∷ Sw24 ∷ []) (pw1 c4 (Sw24 ∷ CCZ034 ∷ []) (CCZ023 ∷ Sw24 ∷ []) tt tt Eq.refl) ▸
       at 15 2 (Bx0-31 ∷ Sw24 ∷ []) (lem-comm-SWAP24-BOX⟨0·31⟩ c4) ▸
       at 16 2 [] (lw0 c4 (Sw24 ∷ Sw24 ∷ []) [] tt tt Eq.refl) ▸
       at 2 6 (Bx3-021 ∷ []) (refl) ▸
       at 5 6 (Bx3-021 ∷ []) (refl) ▸
       at 0 6 (Bx0-3421 ∷ []) (refl) ▸ done


-- sym-bc @133441: 2 steps
lem-sym-bc-at133441 : Complete 4 → ⟪ (Bx0-3241 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3421 ∷ []) ⟫ʷ
lem-sym-bc-at133441 c4 = run b0
  where
  b0 : Chain (Bx0-3241 ∷ []) (Bx0-3421 ∷ [])
  b0 = at 0 1 (Sw24 ∷ Bx0-3241 ∷ Sw24 ∷ []) (sym (lem-SWbc-box-at133441 c4)) ▸
       at 0 3 (Bx0-3421 ∷ []) (lem-nat-SWbc-at133441 c4) ▸ done


-- tP @13243241: 7 steps
lem-tP-at13243241 : Complete 4 → ⟪ (Toff034 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ Toff034 ∷ []) ⟫ʷ
lem-tP-at13243241 c4 = run b0
  where
  b0 : Chain (Toff034 ∷ Toff012 ∷ []) (Toff012 ∷ Toff034 ∷ [])
  b0 = at 0 1 (K0 ∷ CCZ034 ∷ K0⁻ ∷ []) (pw1 c4 (Toff034 ∷ []) (K0 ∷ CCZ034 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (lw4 c4 (Toff012 ∷ []) (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (K0⁻ ∷ K0 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ CCZ034 ∷ []) (lem-cQ-at13243241 c4) ▸
       at 2 0 (K0⁻ ∷ K0 ∷ []) (lw4 c4 [] (K0⁻ ∷ K0 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Toff012 ∷ []) (lw4 c4 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (Toff012 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Toff034 ∷ []) (pw1 c4 (K0 ∷ CCZ034 ∷ K0⁻ ∷ []) (Toff034 ∷ []) tt tt Eq.refl) ▸ done


-- P-box @13243241: 8 steps
lem-P-box-at13243241 : Complete 4 → ⟪ (Toff012 ∷ Bx0-3421 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3421 ∷ []) ⟫ʷ
lem-P-box-at13243241 c4 = run b0
  where
  b0 : Chain (Toff012 ∷ Bx0-3421 ∷ Toff012 ∷ []) (Bx0-3421 ∷ [])
  b0 = at 1 1 (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ []) (lem-box-tQ-at13243241 c4) ▸
       at 0 2 (Toff034 ∷ Toff012 ∷ []) (sym (lem-tP-at13243241 c4)) ▸
       at 1 2 (CCZ012 ∷ CZ12 ∷ Toff012 ∷ []) (lw4 c4 (Toff012 ∷ CCZ012 ∷ []) (CCZ012 ∷ CZ12 ∷ Toff012 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff034 ∷ Toff012 ∷ []) (sym (lem-tP-at13243241 c4)) ▸
       at 4 3 (CCZ012 ∷ CZ12 ∷ []) (lw4 c4 (Toff012 ∷ CCZ012 ∷ Toff012 ∷ []) (CCZ012 ∷ CZ12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff034 ∷ CZ12 ∷ []) (lem-comm-CZ12-TOFF034 c4) ▸
       at 3 3 (CCZ012 ∷ []) (lw4 c4 (CZ12 ∷ CCZ012 ∷ CZ12 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx0-3421 ∷ []) (sym (lem-box-tQ-at13243241 c4)) ▸ done


-- VPQ @13243241: 14 steps
lem-VPQ-at13243241 : Complete 4 → ⟪ (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ []) ⟫ʷ
lem-VPQ-at13243241 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ []) (CS12⁻ ∷ CS34⁻ ∷ S0 ∷ Toff012 ∷ Toff034 ∷ S0⁻ ∷ [])
  b0 = at 0 2 (CS34⁻ ∷ S0 ∷ Toff034 ∷ S0⁻ ∷ []) (pw1 c4 (Toff034 ∷ CCZ034 ∷ []) (CS34⁻ ∷ S0 ∷ Toff034 ∷ S0⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ []) (lw4 c4 (Toff012 ∷ CCZ012 ∷ []) (CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS12⁻ ∷ S0⁻ ∷ []) (c₁ (S • S • S) (CS • CS • CS)) ▸
       at 2 2 (CS12⁻ ∷ Toff034 ∷ []) (lem-comm-TOFF034-CSd12 c4) ▸
       at 1 2 (CS12⁻ ∷ S0 ∷ []) (c₁ (S) (CS • CS • CS)) ▸
       at 0 2 (CS12⁻ ∷ CS34⁻ ∷ []) (sym (c₃ ((CS • CS • CS) ↑) (CS • CS • CS))) ▸
       at 4 2 [] (lw4 c4 (S0⁻ ∷ S0 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 (Toff012 ∷ Toff034 ∷ []) (lem-tP-at13243241 c4) ▸ done

  b1 : Chain (CS12⁻ ∷ CS34⁻ ∷ S0 ∷ Toff012 ∷ Toff034 ∷ S0⁻ ∷ []) (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ [])
  b1 = at 4 0 (S0⁻ ∷ S0 ∷ []) (lw4 c4 [] (S0⁻ ∷ S0 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (S0 ∷ CS34⁻ ∷ []) (sym (c₁ (S) ((CS • CS • CS) ↑ ↑))) ▸
       at 2 2 (Toff012 ∷ CS34⁻ ∷ []) (sym (c₃ (Toff) (CS • CS • CS))) ▸
       at 3 2 (S0⁻ ∷ CS34⁻ ∷ []) (sym (c₁ (S • S • S) ((CS • CS • CS) ↑ ↑))) ▸
       at 0 4 (Toff012 ∷ CCZ012 ∷ []) (lw4 c4 (CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ []) (Toff012 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff034 ∷ CCZ034 ∷ []) (pw1 c4 (CS34⁻ ∷ S0 ∷ Toff034 ∷ S0⁻ ∷ []) (Toff034 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸ done


-- QVQ @13243241: 3 steps
lem-QVQ-at13243241 : Complete 4 → ⟪ (CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ Toff034 ∷ CCZ034 ∷ Toff012 ∷ []) ⟫ʷ
lem-QVQ-at13243241 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ012 ∷ []) (Toff012 ∷ Toff034 ∷ CCZ034 ∷ Toff012 ∷ [])
  b0 = at 0 0 (Toff012 ∷ Toff012 ∷ []) (lw4 c4 [] (Toff012 ∷ Toff012 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ []) (sym (lem-VPQ-at13243241 c4)) ▸
       at 4 2 [] (lw4 c4 (CCZ012 ∷ CCZ012 ∷ []) [] tt tt Eq.refl) ▸ done


-- box-cP @13243241: 12 steps
lem-box-cP-at13243241 : Complete 4 → ⟪ (Bx0-3421 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ []) ⟫ʷ
lem-box-cP-at13243241 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-3421 ∷ []) (CCZ034 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ023 ∷ Toff302 ∷ CZ13 ∷ Toff302 ∷ CCZ023 ∷ CZ13 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff034 ∷ Bx3-021 ∷ Toff034 ∷ CCZ034 ∷ Bx3-021 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Toff302 ∷ CCZ023 ∷ Bx0-31 ∷ []) (refl) ▸
       at 4 1 (CZ13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 2 6 (CCZ012 ∷ []) (lw4 c4 (CCZ023 ∷ Toff302 ∷ CZ13 ∷ Toff302 ∷ CCZ023 ∷ CZ13 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Toff302 ∷ CCZ023 ∷ Bx0-31 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 10 1 (CZ13 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ023 ∷ Toff302 ∷ CZ13 ∷ Toff302 ∷ CCZ023 ∷ CZ13 ∷ []) (CCZ034 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ [])
  b1 = at 5 6 (CCZ012 ∷ []) (lw4 c4 (CCZ023 ∷ Toff302 ∷ CZ13 ∷ Toff302 ∷ CCZ023 ∷ CZ13 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff012 ∷ Toff034 ∷ CCZ034 ∷ Toff012 ∷ []) (lem-QVQ-at13243241 c4) ▸
       at 1 2 (Toff012 ∷ Toff034 ∷ []) (lem-tP-at13243241 c4) ▸
       at 2 2 [] (pw1 c4 (Toff034 ∷ Toff034 ∷ []) [] tt tt Eq.refl) ▸ done


-- pairs @13243241: 4 steps
lem-pairs-at13243241 : Complete 4 → ⟪ (Bx0-3421 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ []) ⟫ʷ
lem-pairs-at13243241 c4 = run b0
  where
  b0 : Chain (Bx0-3421 ∷ []) (Bx0-2134 ∷ [])
  b0 = at 0 1 (Toff012 ∷ Bx0-3421 ∷ Toff012 ∷ []) (sym (lem-P-box-at13243241 c4)) ▸
       at 1 1 (CCZ034 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ []) (lem-box-cP-at13243241 c4) ▸
       at 4 2 [] (lw4 c4 (Toff012 ∷ Toff012 ∷ []) [] tt tt Eq.refl) ▸
       at 0 4 (Bx0-2134 ∷ []) (sym (lem-box-tQ-at1221 c4)) ▸ done


-- sym-ab @1221: 18 steps
lem-sym-ab-at1221 : Complete 4 → ⟪ (Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-sym-ab-at1221 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx0-2134 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx0-14 ∷ Toff012 ∷ CCZ012 ∷ Bx2-034 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ Toff012 ∷ Bx2-034 ∷ Toff012 ∷ CCZ012 ∷ Bx2-034 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff203 ∷ Bx0-24 ∷ Toff203 ∷ CCZ023 ∷ Bx0-24 ∷ []) (refl) ▸
       at 4 1 (CZ24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 2 6 (CCZ034 ∷ []) (pw1 c4 (CCZ023 ∷ Toff203 ∷ CZ24 ∷ Toff203 ∷ CCZ023 ∷ CZ24 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CCZ013 ∷ Toff103 ∷ CZ14 ∷ Toff103 ∷ CCZ013 ∷ CZ14 ∷ []) (pw2 c4 (CCZ034 ∷ []) (CCZ013 ∷ Toff103 ∷ CZ14 ∷ Toff103 ∷ CCZ013 ∷ CZ14 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx0-14 ∷ []) (refl) ▸
       at 7 1 (Bx0-14 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ012 ∷ Toff012 ∷ CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx0-14 ∷ Toff012 ∷ CCZ012 ∷ Bx2-034 ∷ []) (CCZ012 ∷ Toff012 ∷ Bx1-034 ∷ Toff012 ∷ CCZ012 ∷ CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx0-14 ∷ [])
  b1 = at 2 6 (Bx1-034 ∷ []) (refl) ▸
       at 5 1 (CCZ023 ∷ Toff203 ∷ Bx0-24 ∷ Toff203 ∷ CCZ023 ∷ Bx0-24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 10 1 (CZ24 ∷ []) (refl) ▸
       at 5 6 (CCZ034 ∷ []) (pw1 c4 (CCZ023 ∷ Toff203 ∷ CZ24 ∷ Toff203 ∷ CCZ023 ∷ CZ24 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ013 ∷ Toff103 ∷ CZ14 ∷ Toff103 ∷ CCZ013 ∷ CZ14 ∷ []) (pw2 c4 (CCZ034 ∷ []) (CCZ013 ∷ Toff103 ∷ CZ14 ∷ Toff103 ∷ CCZ013 ∷ CZ14 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Bx0-14 ∷ []) (refl) ▸
       at 10 1 (Bx0-14 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ012 ∷ Toff012 ∷ Bx1-034 ∷ Toff012 ∷ CCZ012 ∷ CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx0-14 ∷ []) (Bx0-1234 ∷ [])
  b2 = at 5 6 (Bx1-034 ∷ []) (refl) ▸
       at 0 6 (Bx0-1234 ∷ []) (refl) ▸ done


-- box-perm-4123 @12233441: 4 steps
lem-box-perm-4123-at12233441 : Complete 4 → ⟪ (Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-box-perm-4123-at12233441 c4 = run b0
  where
  b0 : Chain (Bx0-2341 ∷ []) (Bx0-1234 ∷ [])
  b0 = at 0 1 (Bx0-3241 ∷ []) (lem-sym-ab-at12233441 c4) ▸
       at 0 1 (Bx0-3421 ∷ []) (lem-sym-bc-at133441 c4) ▸
       at 0 1 (Bx0-2134 ∷ []) (lem-pairs-at13243241 c4) ▸
       at 0 1 (Bx0-1234 ∷ []) (lem-sym-ab-at1221 c4) ▸ done


-- box-box-1: 105 steps
lem-box-box-1 : Complete 4 → ⟪ (Bx0-1234 ∷ Bx1-0234 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0234 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-box-box-1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (run b13)))))))))))))
  where
  b0 : Chain (Bx0-1234 ∷ Bx1-0234 ∷ []) (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ012 ∷ Toff134 ∷ CCZ014 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CCZ012 ∷ CX03 ∷ CS04 ∷ Toff134 ∷ [])
  b0 = at 0 1 (Bx0-2341 ∷ []) (lem-box-perm-2341 c4) ▸
       at 0 1 (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) (lem-box-tQ-at12233441 c4) ▸
       at 4 1 (CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff134 ∷ []) (lem-box-cP-at0110 c4) ▸
       at 3 2 (CCZ012 ∷ CCZ014 ∷ []) (pw3 c4 (CCZ014 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff134 ∷ CCZ014 ∷ CCZ034 ∷ []) (pw2 c4 (CCZ014 ∷ Toff134 ∷ []) (Toff134 ∷ CCZ014 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ []) (pw1 c4 (CCZ034 ∷ []) (CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (CCZ012 ∷ CS04 ∷ []) (pw3 c4 (CS04 ∷ CCZ012 ∷ []) (CCZ012 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ012 ∷ CX03 ∷ []) (lw4 c4 (CX03 ∷ CCZ012 ∷ []) (CCZ012 ∷ CX03 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ012 ∷ Toff134 ∷ CCZ014 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CCZ012 ∷ CX03 ∷ CS04 ∷ Toff134 ∷ []) (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff134 ∷ CCZ014 ∷ [])
  b1 = at 8 2 (CCZ012 ∷ CS34⁻ ∷ []) (sym (c₃ (CCZ) (CS • CS • CS))) ▸
       at 7 2 (CCZ012 ∷ CX03 ∷ []) (lw4 c4 (CX03 ∷ CCZ012 ∷ []) (CCZ012 ∷ CX03 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ012 ∷ CS34 ∷ []) (sym (c₃ (CCZ) (CS))) ▸
       at 7 5 (CCZ034 ∷ []) (pw1 c4 (CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ012 ∷ CCZ014 ∷ []) (pw3 c4 (CCZ014 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (Toff134 ∷ CCZ014 ∷ []) (pw2 c4 (CCZ014 ∷ CCZ034 ∷ Toff134 ∷ []) (Toff134 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 3 4 (Bx1-0234 ∷ []) (sym (lem-box-cP-at0110 c4)) ▸
       at 3 1 (CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff134 ∷ []) (lem-box-cP-at0110 c4) ▸ done

  b2 : Chain (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff134 ∷ CCZ014 ∷ []) (Toff023 ∷ CCZ014 ∷ CCZ012 ∷ K0 ∷ CS23 ∷ Toff134 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0⁻ ∷ CCZ123 ∷ CCZ234 ∷ CCZ012 ∷ Toff134 ∷ CCZ014 ∷ [])
  b2 = at 2 2 (CCZ012 ∷ Toff023 ∷ CCZ123 ∷ []) (lw4 c4 (Toff023 ∷ CCZ012 ∷ []) (CCZ012 ∷ Toff023 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff134 ∷ CCZ123 ∷ CCZ234 ∷ []) (lw0 c4 (CCZ123 ∷ Toff134 ∷ []) (Toff134 ∷ CCZ123 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0⁻ ∷ []) (lw4 c4 (Toff023 ∷ []) (K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Toff134 ∷ K0⁻ ∷ []) (c₁ (K • iI) (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑)) ▸
       at 8 2 (Toff134 ∷ CS03 ∷ []) (pw2 c4 (CS03 ∷ Toff134 ∷ []) (Toff134 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff134 ∷ CX02 ∷ []) (lem-comm-CX02-TOFF134 c4) ▸
       at 6 2 (Toff134 ∷ CS23⁻ ∷ []) (lw0 c4 (CS23⁻ ∷ Toff134 ∷ []) (Toff134 ∷ CS23⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff134 ∷ CX02 ∷ []) (lem-comm-CX02-TOFF134 c4) ▸ done

  b3 : Chain (Toff023 ∷ CCZ014 ∷ CCZ012 ∷ K0 ∷ CS23 ∷ Toff134 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0⁻ ∷ CCZ123 ∷ CCZ234 ∷ CCZ012 ∷ Toff134 ∷ CCZ014 ∷ []) (Toff023 ∷ CCZ014 ∷ CCZ012 ∷ Toff134 ∷ Toff023 ∷ CCZ123 ∷ CS34 ∷ CCZ012 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ Toff134 ∷ CCZ014 ∷ [])
  b3 = at 4 2 (Toff134 ∷ CS23 ∷ []) (lw0 c4 (CS23 ∷ Toff134 ∷ []) (Toff134 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff134 ∷ K0 ∷ []) (c₁ (K) (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑)) ▸
       at 4 7 (Toff023 ∷ []) (lw4 c4 (K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0⁻ ∷ []) (Toff023 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) (lw0 c4 (CCZ234 ∷ []) (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (CCZ012 ∷ CS24 ∷ []) (pw3 c4 (CS24 ∷ CCZ012 ∷ []) (CCZ012 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ012 ∷ CX23 ∷ []) (lw4 c4 (CX23 ∷ CCZ012 ∷ []) (CCZ012 ∷ CX23 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ012 ∷ CS34⁻ ∷ []) (sym (c₃ (CCZ) (CS • CS • CS))) ▸
       at 7 2 (CCZ012 ∷ CX23 ∷ []) (lw4 c4 (CX23 ∷ CCZ012 ∷ []) (CCZ012 ∷ CX23 ∷ []) tt tt Eq.refl) ▸ done

  b4 : Chain (Toff023 ∷ CCZ014 ∷ CCZ012 ∷ Toff134 ∷ Toff023 ∷ CCZ123 ∷ CS34 ∷ CCZ012 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ Toff134 ∷ CCZ014 ∷ []) (Toff023 ∷ CCZ014 ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Toff134 ∷ K0⁻ ∷ CCZ234 ∷ CCZ014 ∷ [])
  b4 = at 6 2 (CCZ012 ∷ CS34 ∷ []) (sym (c₃ (CCZ) (CS))) ▸
       at 7 5 (CCZ234 ∷ []) (lw0 c4 (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ012 ∷ CCZ123 ∷ []) (lw4 c4 (CCZ123 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ012 ∷ Toff023 ∷ CCZ123 ∷ []) (lw4 c4 (Toff023 ∷ CCZ012 ∷ []) (CCZ012 ∷ Toff023 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (Toff023 ∷ []) (lw4 c4 (Toff023 ∷ CCZ123 ∷ CCZ123 ∷ []) (Toff023 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff134 ∷ CCZ234 ∷ []) (lw0 c4 (CCZ234 ∷ Toff134 ∷ []) (Toff134 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0⁻ ∷ []) (lw4 c4 (Toff023 ∷ []) (K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 11 2 (Toff134 ∷ K0⁻ ∷ []) (c₁ (K • iI) (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑)) ▸ done

  b5 : Chain (Toff023 ∷ CCZ014 ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Toff134 ∷ K0⁻ ∷ CCZ234 ∷ CCZ014 ∷ []) (Toff023 ∷ CCZ014 ∷ Bx1-0234 ∷ Toff023 ∷ CCZ234 ∷ CCZ014 ∷ [])
  b5 = at 10 2 (Toff134 ∷ CS03 ∷ []) (pw2 c4 (CS03 ∷ Toff134 ∷ []) (Toff134 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Toff134 ∷ CX02 ∷ []) (lem-comm-CX02-TOFF134 c4) ▸
       at 8 2 (Toff134 ∷ CS23⁻ ∷ []) (lw0 c4 (CS23⁻ ∷ Toff134 ∷ []) (Toff134 ∷ CS23⁻ ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff134 ∷ CX02 ∷ []) (lem-comm-CX02-TOFF134 c4) ▸
       at 6 2 (Toff134 ∷ CS23 ∷ []) (lw0 c4 (CS23 ∷ Toff134 ∷ []) (Toff134 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff134 ∷ K0 ∷ []) (c₁ (K) (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑)) ▸
       at 6 7 (Toff023 ∷ []) (lw4 c4 (K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0⁻ ∷ []) (Toff023 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Bx1-0234 ∷ []) (sym (lem-box-cP-at0110 c4)) ▸ done

  b6 : Chain (Toff023 ∷ CCZ014 ∷ Bx1-0234 ∷ Toff023 ∷ CCZ234 ∷ CCZ014 ∷ []) (Toff023 ∷ CCZ012 ∷ Toff134 ∷ CCZ014 ∷ CS34 ∷ CCZ012 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Toff134 ∷ Toff023 ∷ CCZ234 ∷ CCZ014 ∷ [])
  b6 = at 2 1 (CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff134 ∷ []) (lem-box-cP-at0110 c4) ▸
       at 1 2 (CCZ012 ∷ CCZ014 ∷ []) (pw3 c4 (CCZ014 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff134 ∷ CCZ014 ∷ CCZ034 ∷ []) (pw2 c4 (CCZ014 ∷ Toff134 ∷ []) (Toff134 ∷ CCZ014 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ []) (pw1 c4 (CCZ034 ∷ []) (CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ012 ∷ CS04 ∷ []) (pw3 c4 (CS04 ∷ CCZ012 ∷ []) (CCZ012 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ012 ∷ CX03 ∷ []) (lw4 c4 (CX03 ∷ CCZ012 ∷ []) (CCZ012 ∷ CX03 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ012 ∷ CS34⁻ ∷ []) (sym (c₃ (CCZ) (CS • CS • CS))) ▸
       at 5 2 (CCZ012 ∷ CX03 ∷ []) (lw4 c4 (CX03 ∷ CCZ012 ∷ []) (CCZ012 ∷ CX03 ∷ []) tt tt Eq.refl) ▸ done

  b7 : Chain (Toff023 ∷ CCZ012 ∷ Toff134 ∷ CCZ014 ∷ CS34 ∷ CCZ012 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Toff134 ∷ Toff023 ∷ CCZ234 ∷ CCZ014 ∷ []) (CCZ012 ∷ Toff023 ∷ Toff134 ∷ CCZ123 ∷ CCZ234 ∷ CCZ012 ∷ Toff134 ∷ CCZ014 ∷ Toff023 ∷ CCZ234 ∷ CCZ014 ∷ [])
  b7 = at 4 2 (CCZ012 ∷ CS34 ∷ []) (sym (c₃ (CCZ) (CS))) ▸
       at 5 5 (CCZ034 ∷ []) (pw1 c4 (CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ012 ∷ CCZ014 ∷ []) (pw3 c4 (CCZ014 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (Toff134 ∷ CCZ014 ∷ []) (pw2 c4 (CCZ014 ∷ CCZ034 ∷ Toff134 ∷ []) (Toff134 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (Bx1-0234 ∷ []) (sym (lem-box-cP-at0110 c4)) ▸
       at 1 1 (CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff134 ∷ []) (lem-box-cP-at0110 c4) ▸
       at 0 2 (CCZ012 ∷ Toff023 ∷ CCZ123 ∷ []) (lw4 c4 (Toff023 ∷ CCZ012 ∷ []) (CCZ012 ∷ Toff023 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff134 ∷ CCZ123 ∷ CCZ234 ∷ []) (lw0 c4 (CCZ123 ∷ Toff134 ∷ []) (Toff134 ∷ CCZ123 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸ done

  b8 : Chain (CCZ012 ∷ Toff023 ∷ Toff134 ∷ CCZ123 ∷ CCZ234 ∷ CCZ012 ∷ Toff134 ∷ CCZ014 ∷ Toff023 ∷ CCZ234 ∷ CCZ014 ∷ []) (CCZ012 ∷ Toff134 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0⁻ ∷ CCZ123 ∷ CCZ234 ∷ CCZ012 ∷ Toff134 ∷ CCZ014 ∷ Toff023 ∷ CCZ234 ∷ CCZ014 ∷ [])
  b8 = at 1 1 (K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0⁻ ∷ []) (lw4 c4 (Toff023 ∷ []) (K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff134 ∷ K0⁻ ∷ []) (c₁ (K • iI) (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑)) ▸
       at 6 2 (Toff134 ∷ CS03 ∷ []) (pw2 c4 (CS03 ∷ Toff134 ∷ []) (Toff134 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff134 ∷ CX02 ∷ []) (lem-comm-CX02-TOFF134 c4) ▸
       at 4 2 (Toff134 ∷ CS23⁻ ∷ []) (lw0 c4 (CS23⁻ ∷ Toff134 ∷ []) (Toff134 ∷ CS23⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff134 ∷ CX02 ∷ []) (lem-comm-CX02-TOFF134 c4) ▸
       at 2 2 (Toff134 ∷ CS23 ∷ []) (lw0 c4 (CS23 ∷ Toff134 ∷ []) (Toff134 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff134 ∷ K0 ∷ []) (c₁ (K) (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑)) ▸ done

  b9 : Chain (CCZ012 ∷ Toff134 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0⁻ ∷ CCZ123 ∷ CCZ234 ∷ CCZ012 ∷ Toff134 ∷ CCZ014 ∷ Toff023 ∷ CCZ234 ∷ CCZ014 ∷ []) (CCZ012 ∷ Toff134 ∷ Toff023 ∷ CCZ123 ∷ CCZ012 ∷ CCZ234 ∷ Toff134 ∷ CCZ014 ∷ Toff023 ∷ CCZ234 ∷ CCZ014 ∷ [])
  b9 = at 2 7 (Toff023 ∷ []) (lw4 c4 (K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0⁻ ∷ []) (Toff023 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) (lw0 c4 (CCZ234 ∷ []) (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ012 ∷ CS24 ∷ []) (pw3 c4 (CS24 ∷ CCZ012 ∷ []) (CCZ012 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ012 ∷ CX23 ∷ []) (lw4 c4 (CX23 ∷ CCZ012 ∷ []) (CCZ012 ∷ CX23 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ012 ∷ CS34⁻ ∷ []) (sym (c₃ (CCZ) (CS • CS • CS))) ▸
       at 5 2 (CCZ012 ∷ CX23 ∷ []) (lw4 c4 (CX23 ∷ CCZ012 ∷ []) (CCZ012 ∷ CX23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ012 ∷ CS34 ∷ []) (sym (c₃ (CCZ) (CS))) ▸
       at 5 5 (CCZ234 ∷ []) (lw0 c4 (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸ done

  b10 : Chain (CCZ012 ∷ Toff134 ∷ Toff023 ∷ CCZ123 ∷ CCZ012 ∷ CCZ234 ∷ Toff134 ∷ CCZ014 ∷ Toff023 ∷ CCZ234 ∷ CCZ014 ∷ []) (CCZ012 ∷ Toff134 ∷ CCZ012 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Toff134 ∷ CX02 ∷ CS03 ∷ K0⁻ ∷ CCZ234 ∷ CCZ014 ∷ Toff023 ∷ CCZ234 ∷ CCZ014 ∷ [])
  b10 = at 3 2 (CCZ012 ∷ CCZ123 ∷ []) (lw4 c4 (CCZ123 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ012 ∷ Toff023 ∷ CCZ123 ∷ []) (lw4 c4 (Toff023 ∷ CCZ012 ∷ []) (CCZ012 ∷ Toff023 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (Toff023 ∷ []) (lw4 c4 (Toff023 ∷ CCZ123 ∷ CCZ123 ∷ []) (Toff023 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff134 ∷ CCZ234 ∷ []) (lw0 c4 (CCZ234 ∷ Toff134 ∷ []) (Toff134 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0⁻ ∷ []) (lw4 c4 (Toff023 ∷ []) (K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Toff134 ∷ K0⁻ ∷ []) (c₁ (K • iI) (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑)) ▸
       at 8 2 (Toff134 ∷ CS03 ∷ []) (pw2 c4 (CS03 ∷ Toff134 ∷ []) (Toff134 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff134 ∷ CX02 ∷ []) (lem-comm-CX02-TOFF134 c4) ▸ done

  b11 : Chain (CCZ012 ∷ Toff134 ∷ CCZ012 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Toff134 ∷ CX02 ∷ CS03 ∷ K0⁻ ∷ CCZ234 ∷ CCZ014 ∷ Toff023 ∷ CCZ234 ∷ CCZ014 ∷ []) (Bx1-0234 ∷ Toff023 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CCZ014 ∷ CS24 ∷ Toff023 ∷ CCZ234 ∷ CCZ014 ∷ [])
  b11 = at 6 2 (Toff134 ∷ CS23⁻ ∷ []) (lw0 c4 (CS23⁻ ∷ Toff134 ∷ []) (Toff134 ∷ CS23⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff134 ∷ CX02 ∷ []) (lem-comm-CX02-TOFF134 c4) ▸
       at 4 2 (Toff134 ∷ CS23 ∷ []) (lw0 c4 (CS23 ∷ Toff134 ∷ []) (Toff134 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff134 ∷ K0 ∷ []) (c₁ (K) (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑)) ▸
       at 4 7 (Toff023 ∷ []) (lw4 c4 (K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0⁻ ∷ []) (Toff023 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx1-0234 ∷ []) (sym (lem-box-cP-at0110 c4)) ▸
       at 2 1 (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) (lw0 c4 (CCZ234 ∷ []) (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ014 ∷ CS24 ∷ []) (pw3 c4 (CS24 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS24 ∷ []) tt tt Eq.refl) ▸ done

  b12 : Chain (Bx1-0234 ∷ Toff023 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CCZ014 ∷ CS24 ∷ Toff023 ∷ CCZ234 ∷ CCZ014 ∷ []) (Bx1-0234 ∷ Bx0-2341 ∷ [])
  b12 = at 5 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 c4) ▸
       at 4 2 (CCZ014 ∷ CS34⁻ ∷ []) (pw2 c4 (CS34⁻ ∷ CCZ014 ∷ []) (CCZ014 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 c4) ▸
       at 2 2 (CCZ014 ∷ CS34 ∷ []) (pw2 c4 (CS34 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 3 5 (CCZ234 ∷ []) (lw0 c4 (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff023 ∷ CCZ234 ∷ []) (pw1 c4 (CCZ234 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw0 c4 (CCZ234 ∷ CCZ234 ∷ []) [] tt tt Eq.refl) ▸
       at 1 4 (Bx0-2341 ∷ []) (sym (lem-box-tQ-at12233441 c4)) ▸ done

  b13 : Chain (Bx1-0234 ∷ Bx0-2341 ∷ []) (Bx1-0234 ∷ Bx0-1234 ∷ [])
  b13 = at 1 1 (Bx0-1234 ∷ []) (lem-box-perm-4123-at12233441 c4) ▸ done


-- cQ @233442: 7 steps
lem-cQ-at233442 : Complete 4 → ⟪ (CCZ013 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ CCZ013 ∷ []) ⟫ʷ
lem-cQ-at233442 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ013 ∷ [])
  b0 = at 0 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (lw4 c4 (CCZ013 ∷ []) (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ024 ∷ CS01 ∷ []) (pw3 c4 (CS01 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 2 2 (CCZ024 ∷ CS03⁻ ∷ []) (pw1 c4 (CS03⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS03⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 0 2 (CCZ024 ∷ CS03 ∷ []) (pw1 c4 (CS03 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 1 5 (CCZ013 ∷ []) (lw4 c4 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸ done


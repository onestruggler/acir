{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R036 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-1-CCZ014)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-CCZ014)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-0-CCZ034 ; lem-nat-0-CCZ134)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-0-BOX⟨0·42⟩ ; lem-nat-1-BOX⟨1·42⟩)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-0-TOFF401 ; lem-nat-1-TOFF401)
open import Examples.Groups.Clifford+CS.Five.D.R013 using (lem-nat-0-BOX⟨1·42⟩ ; lem-nat-3-CS13 ; lem-nat-3-CS14 ; lem-nat-3-CSd13 ; lem-nat-3-CSd14)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-0-TOFF134)
open import Examples.Groups.Clifford+CS.Five.D.R016 using (lem-nat-0-TOFF034)
-- comm CCZ023 CS14: 145 steps
lem-comm-CCZ023-CS14 : Complete 4 → ⟪ (CCZ023 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CCZ023 ∷ []) ⟫ʷ
lem-comm-CCZ023-CS14 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (run b18))))))))))))))))))
  where
  b0 : Chain (CCZ023 ∷ CS14 ∷ []) (Sw12 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 1 (Sw12 ∷ CCZ013 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw34 ∷ []) (CS23 ∷ CX02 ∷ Sw12 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw34 ∷ [])
  b1 = at 3 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 0 2 (CS23 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS13 ∷ []) (CS23 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (CS23 ∷ CX02 ∷ Sw12 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw34 ∷ []) (CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw34 ∷ CX02 ∷ CS04 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw34 ∷ [])
  b2 = at 2 2 (CS23⁻ ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS13⁻ ∷ []) (CS23⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS03 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS03 ∷ []) (CS03 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸
       at 4 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw34 ∷ CX02 ∷ []) (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap)) ▸ done

  b3 : Chain (CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw34 ∷ CX02 ∷ CS04 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw12 ∷ CS14 ∷ Sw12 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw34 ∷ [])
  b3 = at 2 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw34 ∷ CX02 ∷ []) (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap)) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (CS24 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CS14 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS24 ∷ []) (CS14 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (Sw34 ∷ Sw12 ∷ CS14 ∷ Sw12 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw12 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw34 ∷ [])
  b4 = at 3 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸
       at 4 2 (CS14⁻ ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS24⁻ ∷ []) (CS14⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸
       at 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 7 2 (CS03 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS03 ∷ []) (CS03 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸ done

  b5 : Chain (Sw34 ∷ Sw12 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw12 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw34 ∷ CS04 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw34 ∷ [])
  b5 = at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 6 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸ done

  b6 : Chain (Sw34 ∷ Sw12 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw34 ∷ CS04 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw34 ∷ [])
  b6 = at 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done

  b7 : Chain (Sw34 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw23 ∷ Sw23 ∷ CCZ024 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw34 ∷ [])
  b7 = at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 4 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (CCZ014 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (CCZ024 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸ done

  b8 : Chain (Sw34 ∷ Sw23 ∷ Sw23 ∷ CCZ024 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ CS34 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ [])
  b8 = at 2 3 (CCZ034 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 10 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CS23 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS13 ∷ []) (CS23 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 10 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 8 3 (CS24 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CS34 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS24 ∷ []) (CS34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸ done

  b9 : Chain (Sw34 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ CS34 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw23 ∷ CS12 ∷ CCZ034 ∷ Sw23 ∷ Sw34 ∷ [])
  b9 = at 6 2 (CS34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CS)) ▸
       at 5 2 (CS24 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS34 ∷ []) (CS24 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 (CS13 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS23 ∷ []) (CS13 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 3 9 (CCZ034 ∷ []) (by-assoc Eq.refl) ▸ done

  b10 : Chain (Sw34 ∷ Sw23 ∷ CS12 ∷ CCZ034 ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ [])
  b10 = at 3 1 (Sw23 ∷ CCZ024 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 4 1 (Sw12 ∷ CCZ014 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (Sw34 ∷ CCZ013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b11 : Chain (Sw34 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ []) (Sw34 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ Sw34 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ [])
  b11 = at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 8 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 10 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸ done

  b12 : Chain (Sw34 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ Sw34 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ []) (Sw34 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw12 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw12 ∷ Sw34 ∷ [])
  b12 = at 5 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 9 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 7 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 11 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 9 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done

  b13 : Chain (Sw34 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw12 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw12 ∷ Sw34 ∷ []) (Sw34 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ Sw12 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ [])
  b13 = at 4 2 (CS24 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS14 ∷ []) (CS24 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 7 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS24⁻ ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS14⁻ ∷ []) (CS24⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 9 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 7 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 9 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸ done

  b14 : Chain (Sw34 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ Sw12 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ []) (Sw34 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CS24 ∷ CX02 ∷ Sw34 ∷ CS23⁻ ∷ Sw34 ∷ Sw34 ∷ CX02 ∷ CS03 ∷ [])
  b14 = at 9 2 (CS03 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS03 ∷ []) (CS03 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 8 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸
       at 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 (Sw34 ∷ CX02 ∷ []) (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap)) ▸
       at 6 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b15 : Chain (Sw34 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CS24 ∷ CX02 ∷ Sw34 ∷ CS23⁻ ∷ Sw34 ∷ Sw34 ∷ CX02 ∷ CS03 ∷ []) (Sw34 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ CS13 ∷ CX01 ∷ Sw12 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ [])
  b15 = at 8 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 (Sw34 ∷ CX02 ∷ []) (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap)) ▸
       at 4 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 5 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CS13 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS23 ∷ []) (CS13 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 8 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done

  b16 : Chain (Sw34 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ CS13 ∷ CX01 ∷ Sw12 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ []) (Sw34 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ Sw23 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw12 ∷ [])
  b16 = at 8 2 (CS13⁻ ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS23⁻ ∷ []) (CS13⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 10 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸
       at 10 2 (CS03 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS03 ∷ []) (CS03 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸ done

  b17 : Chain (Sw34 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ Sw23 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw12 ∷ []) (Sw34 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw34 ∷ CCZ023 ∷ [])
  b17 = at 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 10 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 7 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 6 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸ done

  b18 : Chain (Sw34 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw34 ∷ CCZ023 ∷ []) (CS14 ∷ CCZ023 ∷ [])
  b18 = at 0 5 (CS14 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CCZ013 CS24: 15 steps
lem-comm-CCZ013-CS24 : Complete 4 → ⟪ (CCZ013 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CCZ013 ∷ []) ⟫ʷ
lem-comm-CCZ013-CS24 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ013 ∷ CS24 ∷ []) (Sw34 ∷ Sw34 ∷ Sw23 ∷ CS34 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (CCZ014 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CS24 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS34 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS24 ∷ []) (CS34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CS)) ▸ done

  b1 : Chain (Sw34 ∷ Sw34 ∷ Sw23 ∷ CS34 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ []) (CS24 ∷ CCZ013 ∷ [])
  b1 = at 2 2 (CS24 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS34 ∷ []) (CS24 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 2 5 (CCZ014 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ CCZ013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 0 3 (CS24 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CK40 CCZ123: 13 steps
lem-comm-CK40-CCZ123 : Complete 4 → ⟪ (CK40 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CK40 ∷ []) ⟫ʷ
lem-comm-CK40-CCZ123 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CK40 ∷ CCZ123 ∷ []) (Sw34 ∷ Sw23 ∷ CCZ134 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (CCZ124 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CCZ234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ134 ∷ []) (CCZ234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ234 ∷ CK10 ∷ []) (c₂ (CK₁₀) (CCZ)) ▸
       at 2 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ CCZ134 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (CCZ123 ∷ CK40 ∷ [])
  b1 = at 2 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 1 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 1 7 (CK40 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CCZ123 CK40: 13 steps
lem-comm-CCZ123-CK40 : Complete 4 → ⟪ (CCZ123 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ CCZ123 ∷ []) ⟫ʷ
lem-comm-CCZ123-CK40 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ123 ∷ CK40 ∷ []) (Sw34 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ CCZ134 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (CCZ124 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw12 ∷ CCZ234 ∷ []) (lw0 c4 (CCZ134 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CK10 ∷ CCZ234 ∷ []) (sym (c₂ (CK₁₀) (CCZ))) ▸
       at 4 2 (Sw12 ∷ CCZ134 ∷ []) (lw0 c4 (CCZ234 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ CCZ134 ∷ Sw23 ∷ Sw34 ∷ []) (CK40 ∷ CCZ123 ∷ [])
  b1 = at 5 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 6 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 0 7 (CK40 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CK40 at 3: 20 steps
lem-resp-CK40-at-3 : Complete 4 → ⟪ (CK40 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CK40-at-3 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CK40 ∷ []) (Sw23 ∷ CK40 ∷ Sw23 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (lw0 c4 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 3 2 (Sw34 ∷ CK10 ∷ []) (c₂ (CK₁₀) (Swap ↑)) ▸
       at 2 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 0 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (lw0 c4 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 7 (CK40 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ CK40 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ CK30 ∷ Sw34 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b1 = at 2 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 2 2 (Sw12 ∷ CK30 ∷ []) (lw4 c4 (CK30 ∷ Sw12 ∷ []) (Sw12 ∷ CK30 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 2 3 (CK40 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ CK30 ∷ Sw34 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b2 = at 4 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 3 2 (Sw01 ∷ CK31 ∷ []) (lw4 c4 (CK30 ∷ Sw01 ∷ []) (Sw01 ∷ CK31 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 3 3 (CK41 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CK41 TOFF203: 7 steps
lem-comm-CK41-TOFF203 : Complete 4 → ⟪ (CK41 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CK41 ∷ []) ⟫ʷ
lem-comm-CK41-TOFF203 c4 = run b0
  where
  b0 : Chain (CK41 ∷ Toff203 ∷ []) (Toff203 ∷ CK41 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ CK42 ∷ []) (lw0 c4 (CK41 ∷ Sw12 ∷ []) (Sw12 ∷ CK42 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sw23 ∷ CK43 ∷ []) (lw0 c4 (CK42 ∷ Sw23 ∷ []) (Sw23 ∷ CK43 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff102 ∷ CK43 ∷ []) (sym (c₃ (K ↑ • CCZ • K ↑ • iI) (CK₁₀))) ▸
       at 3 2 (Sw23 ∷ CK42 ∷ []) (lw0 c4 (CK43 ∷ Sw23 ∷ []) (Sw23 ∷ CK42 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sw12 ∷ CK41 ∷ []) (lw0 c4 (CK42 ∷ Sw12 ∷ []) (Sw12 ∷ CK41 ∷ []) tt tt Eq.refl) ▸
       at 0 5 (Toff203 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CCZ023 CK41: 145 steps
lem-comm-CCZ023-CK41 : Complete 4 → ⟪ (CCZ023 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ CCZ023 ∷ []) ⟫ʷ
lem-comm-CCZ023-CK41 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (run b18))))))))))))))))))
  where
  b0 : Chain (CCZ023 ∷ CK41 ∷ []) (Sw12 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 1 (Sw12 ∷ CCZ013 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ []) (CS23 ∷ CX02 ∷ Sw12 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ [])
  b1 = at 3 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 0 2 (CS23 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS13 ∷ []) (CS23 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (CS23 ∷ CX02 ∷ Sw12 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ []) (CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw34 ∷ CX02 ∷ CS04 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ [])
  b2 = at 2 2 (CS23⁻ ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS13⁻ ∷ []) (CS23⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS03 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS03 ∷ []) (CS03 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸
       at 4 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw34 ∷ CX02 ∷ []) (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap)) ▸ done

  b3 : Chain (CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw34 ∷ CX02 ∷ CS04 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw12 ∷ CS14 ∷ Sw12 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ [])
  b3 = at 2 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw34 ∷ CX02 ∷ []) (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap)) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (CS24 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CS14 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS24 ∷ []) (CS14 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (Sw34 ∷ Sw12 ∷ CS14 ∷ Sw12 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw12 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ [])
  b4 = at 3 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸
       at 4 2 (CS14⁻ ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS24⁻ ∷ []) (CS14⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸
       at 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 7 2 (CS03 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS03 ∷ []) (CS03 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸ done

  b5 : Chain (Sw34 ∷ Sw12 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw12 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw34 ∷ CS04 ∷ Sw12 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ [])
  b5 = at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 6 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸ done

  b6 : Chain (Sw34 ∷ Sw12 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw34 ∷ CS04 ∷ Sw12 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ [])
  b6 = at 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done

  b7 : Chain (Sw34 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw23 ∷ Sw23 ∷ CCZ024 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ [])
  b7 = at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 4 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (CCZ014 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (CCZ024 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸ done

  b8 : Chain (Sw34 ∷ Sw23 ∷ Sw23 ∷ CCZ024 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ CK43 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ [])
  b8 = at 2 3 (CCZ034 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 10 3 (CK31 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CK32 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CK31 ∷ []) (CK32 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 10 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 8 3 (CK42 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CK43 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CK42 ∷ []) (CK43 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸ done

  b9 : Chain (Sw34 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ CK43 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw23 ∷ CK21 ∷ CCZ034 ∷ Sw23 ∷ Sw34 ∷ [])
  b9 = at 6 2 (CK43 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CK₁₀)) ▸
       at 5 2 (CK42 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CK43 ∷ []) (CK42 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Sw34 ∷ CK32 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 (CK31 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CK32 ∷ []) (CK31 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 3 9 (CCZ034 ∷ []) (by-assoc Eq.refl) ▸ done

  b10 : Chain (Sw34 ∷ Sw23 ∷ CK21 ∷ CCZ034 ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ [])
  b10 = at 3 1 (Sw23 ∷ CCZ024 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 4 1 (Sw12 ∷ CCZ014 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (Sw34 ∷ CCZ013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b11 : Chain (Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ []) (Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ Sw34 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ [])
  b11 = at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 8 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 10 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸ done

  b12 : Chain (Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ Sw34 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ []) (Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw12 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw12 ∷ Sw34 ∷ [])
  b12 = at 5 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 9 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 7 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 11 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 9 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done

  b13 : Chain (Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw12 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw12 ∷ Sw34 ∷ []) (Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ Sw12 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ [])
  b13 = at 4 2 (CS24 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS14 ∷ []) (CS24 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 7 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS24⁻ ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS14⁻ ∷ []) (CS24⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 9 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 7 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 9 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸ done

  b14 : Chain (Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ Sw12 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ []) (Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ CS24 ∷ CX02 ∷ Sw34 ∷ CS23⁻ ∷ Sw34 ∷ Sw34 ∷ CX02 ∷ CS03 ∷ [])
  b14 = at 9 2 (CS03 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS03 ∷ []) (CS03 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 8 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸
       at 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 (Sw34 ∷ CX02 ∷ []) (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap)) ▸
       at 6 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b15 : Chain (Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ CS24 ∷ CX02 ∷ Sw34 ∷ CS23⁻ ∷ Sw34 ∷ Sw34 ∷ CX02 ∷ CS03 ∷ []) (Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ CS13 ∷ CX01 ∷ Sw12 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ [])
  b15 = at 8 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 (Sw34 ∷ CX02 ∷ []) (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap)) ▸
       at 4 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 5 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CS13 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS23 ∷ []) (CS13 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 8 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done

  b16 : Chain (Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ CS13 ∷ CX01 ∷ Sw12 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ []) (Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ Sw23 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw12 ∷ [])
  b16 = at 8 2 (CS13⁻ ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS23⁻ ∷ []) (CS13⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 10 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸
       at 10 2 (CS03 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS03 ∷ []) (CS03 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸ done

  b17 : Chain (Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ Sw23 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw12 ∷ []) (Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ CCZ023 ∷ [])
  b17 = at 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 10 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 7 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 6 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸ done

  b18 : Chain (Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ CCZ023 ∷ []) (CK41 ∷ CCZ023 ∷ [])
  b18 = at 0 5 (CK41 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CK41 at 3: 6 steps
lem-resp-CK41-at-3 : Complete 4 → ⟪ (CK41 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CK42 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CK41-at-3 c4 = run b0
  where
  b0 : Chain (CK41 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CK42 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Sw23 ∷ CK41 ∷ []) (lw0 c4 (CK41 ∷ Sw23 ∷ []) (Sw23 ∷ CK41 ∷ []) tt tt Eq.refl) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sw12 ∷ CK42 ∷ []) (lw0 c4 (CK41 ∷ Sw12 ∷ []) (Sw12 ∷ CK42 ∷ []) tt tt Eq.refl) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sw01 ∷ CK42 ∷ []) (sym (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑))) ▸ done


-- comm CK41 CCZ023: 7 steps
lem-comm-CK41-CCZ023 : Complete 4 → ⟪ (CK41 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ CK41 ∷ []) ⟫ʷ
lem-comm-CK41-CCZ023 c4 = run b0
  where
  b0 : Chain (CK41 ∷ CCZ023 ∷ []) (CCZ023 ∷ CK41 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ CK42 ∷ []) (lw0 c4 (CK41 ∷ Sw12 ∷ []) (Sw12 ∷ CK42 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sw23 ∷ CK43 ∷ []) (lw0 c4 (CK42 ∷ Sw23 ∷ []) (Sw23 ∷ CK43 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ012 ∷ CK43 ∷ []) (sym (c₃ (CCZ) (CK₁₀))) ▸
       at 3 2 (Sw23 ∷ CK42 ∷ []) (lw0 c4 (CK43 ∷ Sw23 ∷ []) (Sw23 ∷ CK42 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sw12 ∷ CK41 ∷ []) (lw0 c4 (CK42 ∷ Sw12 ∷ []) (Sw12 ∷ CK41 ∷ []) tt tt Eq.refl) ▸
       at 0 5 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CK41 TOFF023: 7 steps
lem-comm-CK41-TOFF023 : Complete 4 → ⟪ (CK41 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CK41 ∷ []) ⟫ʷ
lem-comm-CK41-TOFF023 c4 = run b0
  where
  b0 : Chain (CK41 ∷ Toff023 ∷ []) (Toff023 ∷ CK41 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ CK42 ∷ []) (lw0 c4 (CK41 ∷ Sw12 ∷ []) (Sw12 ∷ CK42 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sw23 ∷ CK43 ∷ []) (lw0 c4 (CK42 ∷ Sw23 ∷ []) (Sw23 ∷ CK43 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff012 ∷ CK43 ∷ []) (sym (c₃ (Toff) (CK₁₀))) ▸
       at 3 2 (Sw23 ∷ CK42 ∷ []) (lw0 c4 (CK43 ∷ Sw23 ∷ []) (Sw23 ∷ CK42 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sw12 ∷ CK41 ∷ []) (lw0 c4 (CK42 ∷ Sw12 ∷ []) (Sw12 ∷ CK41 ∷ []) tt tt Eq.refl) ▸
       at 0 5 (Toff023 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CCZ013 CK42: 15 steps
lem-comm-CCZ013-CK42 : Complete 4 → ⟪ (CCZ013 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ CCZ013 ∷ []) ⟫ʷ
lem-comm-CCZ013-CK42 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ013 ∷ CK42 ∷ []) (Sw34 ∷ Sw34 ∷ Sw23 ∷ CK43 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CK32 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (CCZ014 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CK42 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CK43 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CK42 ∷ []) (CK43 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CK43 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CK₁₀)) ▸ done

  b1 : Chain (Sw34 ∷ Sw34 ∷ Sw23 ∷ CK43 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ []) (CK42 ∷ CCZ013 ∷ [])
  b1 = at 2 2 (CK42 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CK43 ∷ []) (CK42 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sw34 ∷ CK32 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 2 5 (CCZ014 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ CCZ013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 0 3 (CK42 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CK42 TOFF103: 5 steps
lem-comm-CK42-TOFF103 : Complete 4 → ⟪ (CK42 ∷ Toff103 ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ CK42 ∷ []) ⟫ʷ
lem-comm-CK42-TOFF103 c4 = run b0
  where
  b0 : Chain (CK42 ∷ Toff103 ∷ []) (Toff103 ∷ CK42 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ CK43 ∷ []) (lw0 c4 (CK42 ∷ Sw23 ∷ []) (Sw23 ∷ CK43 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff102 ∷ CK43 ∷ []) (sym (c₃ (K ↑ • CCZ • K ↑ • iI) (CK₁₀))) ▸
       at 2 2 (Sw23 ∷ CK42 ∷ []) (lw0 c4 (CK43 ∷ Sw23 ∷ []) (Sw23 ∷ CK42 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Toff103 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CK42 TOFF013: 5 steps
lem-comm-CK42-TOFF013 : Complete 4 → ⟪ (CK42 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CK42 ∷ []) ⟫ʷ
lem-comm-CK42-TOFF013 c4 = run b0
  where
  b0 : Chain (CK42 ∷ Toff013 ∷ []) (Toff013 ∷ CK42 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ CK43 ∷ []) (lw0 c4 (CK42 ∷ Sw23 ∷ []) (Sw23 ∷ CK43 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff012 ∷ CK43 ∷ []) (sym (c₃ (Toff) (CK₁₀))) ▸
       at 2 2 (Sw23 ∷ CK42 ∷ []) (lw0 c4 (CK43 ∷ Sw23 ∷ []) (Sw23 ∷ CK42 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CK42 CCZ013: 5 steps
lem-comm-CK42-CCZ013 : Complete 4 → ⟪ (CK42 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ CK42 ∷ []) ⟫ʷ
lem-comm-CK42-CCZ013 c4 = run b0
  where
  b0 : Chain (CK42 ∷ CCZ013 ∷ []) (CCZ013 ∷ CK42 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ CK43 ∷ []) (lw0 c4 (CK42 ∷ Sw23 ∷ []) (Sw23 ∷ CK43 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ CK43 ∷ []) (sym (c₃ (CCZ) (CK₁₀))) ▸
       at 2 2 (Sw23 ∷ CK42 ∷ []) (lw0 c4 (CK43 ∷ Sw23 ∷ []) (Sw23 ∷ CK42 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp TOFF413 at 2: 4 steps
lem-resp-TOFF413-at-2 : Complete 4 → ⟪ (Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ Toff423 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-TOFF413-at-2 c4 = run b0
  where
  b0 : Chain (Toff413 ∷ []) (Sw12 ∷ Sw01 ∷ Toff423 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Sw12 ∷ Toff423 ∷ []) (lw0 c4 (Toff413 ∷ Sw12 ∷ []) (Sw12 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sw01 ∷ Toff423 ∷ []) (sym (c₂ (Swap) (Toffᵗ))) ▸ done


-- nat 2 SBOX(2;1;4;0): 3 steps
lem-nat-2-SBOX⟨2·1·4·0⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb2-1-4-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-1-4-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨2·1·4·0⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb2-1-4-0 ∷ []) (Sb3-1-4-0 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS14 ∷ []) (refl) ▸
       at 0 2 (CS14 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS14 ∷ []) (CS14 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb3-1-4-0 ∷ []) (refl) ▸ done


-- nat 2 SBOX(3;1;4;0): 3 steps
lem-nat-2-SBOX⟨3·1·4·0⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb3-1-4-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-4-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨3·1·4·0⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb3-1-4-0 ∷ []) (Sb2-1-4-0 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS14 ∷ []) (refl) ▸
       at 0 2 (CS14 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS14 ∷ []) (CS14 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb2-1-4-0 ∷ []) (refl) ▸ done


-- nat 3 SBOX(2;1;3;0): 3 steps
lem-nat-3-SBOX⟨2·1·3·0⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb2-1-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-4-0 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨2·1·3·0⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb2-1-3-0 ∷ []) (Sb2-1-4-0 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS13 ∷ []) (refl) ▸
       at 0 2 (CS14 ∷ Sw34 ∷ []) (lem-nat-3-CS13 c4) ▸
       at 0 1 (Sb2-1-4-0 ∷ []) (refl) ▸ done


-- nat 3 SBOX(2;1;4;0): 3 steps
lem-nat-3-SBOX⟨2·1·4·0⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb2-1-4-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-3-0 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨2·1·4·0⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb2-1-4-0 ∷ []) (Sb2-1-3-0 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS14 ∷ []) (refl) ▸
       at 0 2 (CS13 ∷ Sw34 ∷ []) (lem-nat-3-CS14 c4) ▸
       at 0 1 (Sb2-1-3-0 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(2;1;4;0): 3 steps
lem-nat-2-SBOXd⟨2·1·4·0⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb⁻2-1-4-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-1-4-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨2·1·4·0⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻2-1-4-0 ∷ []) (Sb⁻3-1-4-0 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS14⁻ ∷ []) (refl) ▸
       at 0 2 (CS14⁻ ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻3-1-4-0 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(3;1;4;0): 3 steps
lem-nat-2-SBOXd⟨3·1·4·0⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb⁻3-1-4-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-1-4-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨3·1·4·0⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻3-1-4-0 ∷ []) (Sb⁻2-1-4-0 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS14⁻ ∷ []) (refl) ▸
       at 0 2 (CS14⁻ ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻2-1-4-0 ∷ []) (refl) ▸ done


-- nat 3 SBOXd(2;1;3;0): 3 steps
lem-nat-3-SBOXd⟨2·1·3·0⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb⁻2-1-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-1-4-0 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨2·1·3·0⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻2-1-3-0 ∷ []) (Sb⁻2-1-4-0 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS13⁻ ∷ []) (refl) ▸
       at 0 2 (CS14⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd13 c4) ▸
       at 0 1 (Sb⁻2-1-4-0 ∷ []) (refl) ▸ done


-- nat 3 SBOXd(2;1;4;0): 3 steps
lem-nat-3-SBOXd⟨2·1·4·0⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb⁻2-1-4-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-1-3-0 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨2·1·4·0⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻2-1-4-0 ∷ []) (Sb⁻2-1-3-0 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS14⁻ ∷ []) (refl) ▸
       at 0 2 (CS13⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd14 c4) ▸
       at 0 1 (Sb⁻2-1-3-0 ∷ []) (refl) ▸ done


-- nat 0 BOX(4;012): 8 steps
lem-nat-0-BOX⟨4·012⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx4-012 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-102 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·012⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-012 ∷ []) (Bx4-102 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff401 ∷ Bx0-42 ∷ Toff401 ∷ CCZ014 ∷ Bx0-42 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 1 2 (Toff401 ∷ Sw01 ∷ []) (lem-nat-0-TOFF401 c4) ▸
       at 2 2 (Bx1-42 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·42⟩ c4) ▸
       at 3 2 (Toff401 ∷ Sw01 ∷ []) (lem-nat-0-TOFF401 c4) ▸
       at 4 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 5 2 (Bx1-42 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·42⟩ c4) ▸
       at 0 6 (Bx4-102 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;4312): 8 steps
lem-nat-0-BOX⟨0·4312⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx0-4312 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-4302 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·4312⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-4312 ∷ []) (Bx1-4302 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff034 ∷ Bx4-012 ∷ Toff034 ∷ CCZ034 ∷ Bx4-012 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 1 2 (Toff134 ∷ Sw01 ∷ []) (lem-nat-0-TOFF034 c4) ▸
       at 2 2 (Bx4-102 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·012⟩ c4) ▸
       at 3 2 (Toff134 ∷ Sw01 ∷ []) (lem-nat-0-TOFF034 c4) ▸
       at 4 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 5 2 (Bx4-102 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·012⟩ c4) ▸
       at 0 6 (Bx1-4302 ∷ []) (refl) ▸ done


-- nat 0 BOX(4;102): 8 steps
lem-nat-0-BOX⟨4·102⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx4-102 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-012 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·102⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-102 ∷ []) (Bx4-012 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff401 ∷ Bx1-42 ∷ Toff401 ∷ CCZ014 ∷ Bx1-42 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 1 2 (Toff401 ∷ Sw01 ∷ []) (lem-nat-0-TOFF401 c4) ▸
       at 2 2 (Bx0-42 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·42⟩ c4) ▸
       at 3 2 (Toff401 ∷ Sw01 ∷ []) (lem-nat-0-TOFF401 c4) ▸
       at 4 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 5 2 (Bx0-42 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·42⟩ c4) ▸
       at 0 6 (Bx4-012 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;4302): 8 steps
lem-nat-0-BOX⟨1·4302⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx1-4302 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4312 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·4302⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-4302 ∷ []) (Bx0-4312 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff134 ∷ Bx4-102 ∷ Toff134 ∷ CCZ134 ∷ Bx4-102 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 1 2 (Toff034 ∷ Sw01 ∷ []) (lem-nat-0-TOFF134 c4) ▸
       at 2 2 (Bx4-012 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·102⟩ c4) ▸
       at 3 2 (Toff034 ∷ Sw01 ∷ []) (lem-nat-0-TOFF134 c4) ▸
       at 4 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 5 2 (Bx4-012 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·102⟩ c4) ▸
       at 0 6 (Bx0-4312 ∷ []) (refl) ▸ done


-- nat 1 BOX(4;102): 8 steps
lem-nat-1-BOX⟨4·102⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx4-102 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-201 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·102⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-102 ∷ []) (Bx4-201 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff401 ∷ Bx1-42 ∷ Toff401 ∷ CCZ014 ∷ Bx1-42 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 1 2 (Toff402 ∷ Sw12 ∷ []) (lem-nat-1-TOFF401 c4) ▸
       at 2 2 (Bx2-41 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·42⟩ c4) ▸
       at 3 2 (Toff402 ∷ Sw12 ∷ []) (lem-nat-1-TOFF401 c4) ▸
       at 4 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 5 2 (Bx2-41 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·42⟩ c4) ▸
       at 0 6 (Bx4-201 ∷ []) (refl) ▸ done


-- nat 1 BOX(1;4302): 8 steps
lem-nat-1-BOX⟨1·4302⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx1-4302 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4301 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·4302⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-4302 ∷ []) (Bx2-4301 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff134 ∷ Bx4-102 ∷ Toff134 ∷ CCZ134 ∷ Bx4-102 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ134 ∷ []) (CCZ234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff134 ∷ []) (Toff234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx4-201 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·102⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff134 ∷ []) (Toff234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ134 ∷ []) (CCZ234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx4-201 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·102⟩ c4) ▸
       at 0 6 (Bx2-4301 ∷ []) (refl) ▸ done


-- nat 2 SBOX(2;1;0;4): 2 steps
lem-nat-2-SBOX⟨2·1·0·4⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb2-1-0-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-1-0-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨2·1·0·4⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb2-1-0-4 ∷ []) (Sb3-1-0-4 ∷ Sw23 ∷ [])
  b0 = at 0 2 (Sb2-1-0-4 ∷ Sw23 ∷ []) (sym (c₂ (CS) (Swap))) ▸
       at 0 1 (Sb3-1-0-4 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 SBOX(3;1;0;4): 2 steps
lem-nat-2-SBOX⟨3·1·0·4⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb3-1-0-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-0-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨3·1·0·4⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb3-1-0-4 ∷ []) (Sb2-1-0-4 ∷ Sw23 ∷ [])
  b0 = at 0 2 (Sb3-1-0-4 ∷ Sw23 ∷ []) (sym (c₂ (CS) (Swap))) ▸
       at 0 1 (Sb2-1-0-4 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 SBOX(2;1;0;3): 2 steps
lem-nat-3-SBOX⟨2·1·0·3⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb2-1-0-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-0-4 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨2·1·0·3⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb2-1-0-3 ∷ []) (Sb2-1-0-4 ∷ Sw34 ∷ [])
  b0 = at 0 2 (Sb2-1-0-3 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 0 1 (Sb2-1-0-4 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 SBOX(2;1;0;4): 2 steps
lem-nat-3-SBOX⟨2·1·0·4⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb2-1-0-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-0-3 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨2·1·0·4⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb2-1-0-4 ∷ []) (Sb2-1-0-3 ∷ Sw34 ∷ [])
  b0 = at 0 2 (Sb2-1-0-4 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 0 1 (Sb2-1-0-3 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 SBOX(2;0;1;3): 3 steps
lem-nat-0-SBOX⟨2·0·1·3⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb2-0-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-0-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨2·0·1·3⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb2-0-1-3 ∷ []) (Sb2-1-0-3 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS01 ∷ []) (refl) ▸
       at 0 2 (CS01 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS01 ∷ []) (CS01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb2-1-0-3 ∷ []) (refl) ▸ done


-- nat 0 SBOX(2;1;0;3): 3 steps
lem-nat-0-SBOX⟨2·1·0·3⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb2-1-0-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-1-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨2·1·0·3⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb2-1-0-3 ∷ []) (Sb2-0-1-3 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS01 ∷ []) (refl) ▸
       at 0 2 (CS01 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS01 ∷ []) (CS01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb2-0-1-3 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(2;1;0;4): 2 steps
lem-nat-2-SBOXd⟨2·1·0·4⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb⁻2-1-0-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-1-0-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨2·1·0·4⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻2-1-0-4 ∷ []) (Sb⁻3-1-0-4 ∷ Sw23 ∷ [])
  b0 = at 0 2 (Sb⁻2-1-0-4 ∷ Sw23 ∷ []) (sym (c₂ (CS • CS • CS) (Swap))) ▸
       at 0 1 (Sb⁻3-1-0-4 ∷ []) (by-assoc Eq.refl) ▸ done


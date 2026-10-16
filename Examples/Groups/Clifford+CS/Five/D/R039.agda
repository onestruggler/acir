{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R039 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-2-CCZ012 ; lem-nat-2-CCZ013 ; lem-nat-2-TOFF102 ; lem-nat-2-TOFF103 ; lem-nat-3-CCZ014 ; lem-nat-3-CCZ024 ; lem-nat-3-TOFF104)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-3-CCZ013 ; lem-nat-3-CCZ023)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-CCZ024 ; lem-nat-2-CCZ124 ; lem-nat-2-CCZ134)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-2-TOFF413 ; lem-nat-3-TOFF402)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-0-CCZ034)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-3-TOFF302)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-0-TOFF402 ; lem-nat-2-TOFF104 ; lem-nat-2-TOFF412)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-2-TOFF214)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-3-TOFF103)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-nat-2-CCZ014 ; lem-nat-2-CZ12)
open import Examples.Groups.Clifford+CS.Five.D.R013 using (lem-nat-2-CS12 ; lem-nat-2-CS13 ; lem-nat-2-CSd12 ; lem-nat-2-CSd13 ; lem-nat-2-TOFF314)
open import Examples.Groups.Clifford+CS.Five.D.R016 using (lem-nat-0-TOFF034 ; lem-nat-3-CS04 ; lem-nat-3-CSd04)
open import Examples.Groups.Clifford+CS.Five.D.R017 using (lem-nat-3-CS03 ; lem-nat-3-CSd03)
open import Examples.Groups.Clifford+CS.Five.D.R023 using (lem-nat-2-TOFF134)
open import Examples.Groups.Clifford+CS.Five.D.R024 using (lem-nat-2-BOX⟨3·21⟩)
open import Examples.Groups.Clifford+CS.Five.D.R028 using (lem-nat-2-BOX⟨2·0431⟩ ; lem-nat-3-BOX⟨1·0423⟩)
open import Examples.Groups.Clifford+CS.Five.D.R029 using (lem-nat-3-BOX⟨1·0324⟩)
open import Examples.Groups.Clifford+CS.Five.D.R032 using (lem-nat-2-BOX⟨2·13⟩)
open import Examples.Groups.Clifford+CS.Five.D.R033 using (lem-nat-2-BOX⟨2·31⟩)
open import Examples.Groups.Clifford+CS.Five.D.R037 using (lem-nat-0-BOX⟨0·41⟩ ; lem-nat-2-BOX⟨4·13⟩)
open import Examples.Groups.Clifford+CS.Five.D.R038 using (lem-nat-2-BOX⟨4·12⟩)
-- resp TOFF304 at 2: 236 steps
lem-resp-TOFF304-at-2 : Complete 4 → ⟪ (Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ Toff314 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-TOFF304-at-2 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (run b29)))))))))))))))))))))))))))))
  where
  b0 : Chain (Toff304 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sw23 ∷ Toff204 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw12 ∷ Toff104 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Toff103 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ Sw23 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ [])
  b1 = at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸ done

  b2 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ Sw23 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ Sw34 ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ [])
  b2 = at 10 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 11 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 2 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (Sw23 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ Sw34 ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ []) (Sw23 ∷ K2 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ [])
  b3 = at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 9 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 7 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 9 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 10 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 (K2 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ K1 ∷ []) (K2 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CS24 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS14 ∷ []) (CS24 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸ done

  b4 : Chain (Sw23 ∷ K2 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ []) (Sw23 ∷ K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ [])
  b4 = at 5 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS24⁻ ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS14⁻ ∷ []) (CS24⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 7 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 7 2 (CS03 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS03 ∷ []) (CS03 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸ done

  b5 : Chain (Sw23 ∷ K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ []) (K3 ∷ CS34 ∷ Sw23 ∷ CX02 ∷ Sw23 ∷ Sw23 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ [])
  b5 = at 8 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K2 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ K1 ∷ []) (K2 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 9 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸
       at 0 2 (K3 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ K2 ∷ []) (K3 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS34 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS24 ∷ []) (CS34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸ done

  b6 : Chain (K3 ∷ CS34 ∷ Sw23 ∷ CX02 ∷ Sw23 ∷ Sw23 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ []) (K3 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ [])
  b6 = at 2 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS34⁻ ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS24⁻ ∷ []) (CS34⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (lw0 c4 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 8 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸ done

  b7 : Chain (K3 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ []) (K3 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Sw12 ∷ K3 ∷ ι ∷ Sw12 ∷ [])
  b7 = at 9 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 10 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (lw0 c4 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K3 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ K2 ∷ []) (K3 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 8 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 (Sw12 ∷ ι ∷ []) (c₁ (iI) (Swap)) ▸
       at 6 2 (Sw12 ∷ K3 ∷ []) (sym (c₃ (Swap ↑) (K))) ▸ done

  b8 : Chain (K3 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Sw12 ∷ K3 ∷ ι ∷ Sw12 ∷ []) (K3 ∷ CS34 ∷ Sw12 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K3 ∷ ι ∷ Sw12 ∷ [])
  b8 = at 5 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 6 2 (Sw12 ∷ CS03 ∷ []) (lw4 c4 (CS03 ∷ Sw12 ∷ []) (Sw12 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw12 ∷ CX03 ∷ []) (lw4 c4 (CX03 ∷ Sw12 ∷ []) (Sw12 ∷ CX03 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Sw12 ∷ CS34⁻ ∷ []) (sym (c₃ (Swap ↑) (CS • CS • CS))) ▸
       at 2 2 (Sw12 ∷ CX03 ∷ []) (lw4 c4 (CX03 ∷ Sw12 ∷ []) (Sw12 ∷ CX03 ∷ []) tt tt Eq.refl) ▸ done

  b9 : Chain (K3 ∷ CS34 ∷ Sw12 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K3 ∷ ι ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ Sw23 ∷ CX03 ∷ CS04 ∷ K3 ∷ ι ∷ Sw12 ∷ [])
  b9 = at 1 2 (Sw12 ∷ CS34 ∷ []) (sym (c₃ (Swap ↑) (CS))) ▸
       at 0 2 (Sw12 ∷ K3 ∷ []) (sym (c₃ (Swap ↑) (K))) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (K2 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ K3 ∷ []) (K2 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS24 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS34 ∷ []) (CS24 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 (CS24⁻ ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS34⁻ ∷ []) (CS24⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸ done

  b10 : Chain (Sw12 ∷ Sw23 ∷ K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ Sw23 ∷ CX03 ∷ CS04 ∷ K3 ∷ ι ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw23 ∷ K3 ∷ ι ∷ Sw12 ∷ [])
  b10 = at 7 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 8 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (lw0 c4 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 10 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 11 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 12 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (lw0 c4 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸ done

  b11 : Chain (Sw12 ∷ Sw23 ∷ K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw23 ∷ K3 ∷ ι ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ Sw12 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw12 ∷ [])
  b11 = at 7 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K2 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ K3 ∷ []) (K2 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (K1 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ K2 ∷ []) (K1 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS14 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS24 ∷ []) (CS14 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done

  b12 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ Sw12 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw12 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw12 ∷ [])
  b12 = at 6 2 (CS14⁻ ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS24⁻ ∷ []) (CS14⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 8 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸
       at 9 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 9 2 (CS03 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS03 ∷ []) (CS03 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 8 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done

  b13 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw12 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ Sw34 ∷ Sw34 ∷ CS13⁻ ∷ Sw34 ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ [])
  b13 = at 9 2 (K1 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ K2 ∷ []) (K1 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 3 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 6 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b14 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ Sw34 ∷ Sw34 ∷ CS13⁻ ∷ Sw34 ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K1 ∷ Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ [])
  b14 = at 7 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 10 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 10 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 11 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸ done

  b15 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K1 ∷ Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ [])
  b15 = at 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done

  b16 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Toff304 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b16 = at 11 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 12 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 5 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 4 3 (Toff103 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (Toff104 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff204 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff304 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸ done

  b17 : Chain (Sw12 ∷ Toff304 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b17 = at 1 1 (Sw23 ∷ Toff204 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw12 ∷ Toff104 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ Toff103 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b18 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b18 = at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 7 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 11 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸ done

  b19 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b19 = at 12 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸ done

  b20 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ K2 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b20 = at 10 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 8 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 10 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 11 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 2 2 (K2 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ K1 ∷ []) (K2 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS24 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS14 ∷ []) (CS24 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸ done

  b21 : Chain (Sw12 ∷ Sw23 ∷ K2 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b21 = at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS24⁻ ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS14⁻ ∷ []) (CS24⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 8 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 8 2 (CS03 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS03 ∷ []) (CS03 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸ done

  b22 : Chain (Sw12 ∷ Sw23 ∷ K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ K3 ∷ CS34 ∷ CX03 ∷ Sw23 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b22 = at 7 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K2 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ K1 ∷ []) (K2 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 10 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 (K3 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ K2 ∷ []) (K3 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CS34 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS24 ∷ []) (CS34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸ done

  b23 : Chain (Sw12 ∷ K3 ∷ CS34 ∷ CX03 ∷ Sw23 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ K3 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b23 = at 4 2 (CS34⁻ ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS24⁻ ∷ []) (CS34⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (lw0 c4 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 9 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 10 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸ done

  b24 : Chain (Sw12 ∷ K3 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ K3 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw01 ∷ K3 ∷ ι ∷ Sw01 ∷ Sw12 ∷ [])
  b24 = at 11 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (lw0 c4 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 6 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K3 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ K2 ∷ []) (K3 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 9 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 (Sw01 ∷ ι ∷ []) (lw4 c4 (ι ∷ Sw01 ∷ []) (Sw01 ∷ ι ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Sw01 ∷ K3 ∷ []) (sym (c₂ (Swap) (K ↑))) ▸
       at 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b25 : Chain (Sw12 ∷ K3 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw01 ∷ K3 ∷ ι ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ K3 ∷ Sw01 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3 ∷ ι ∷ Sw01 ∷ Sw12 ∷ [])
  b25 = at 8 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 7 2 (Sw01 ∷ CS13 ∷ []) (lw4 c4 (CS03 ∷ Sw01 ∷ []) (Sw01 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 7 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw01 ∷ CX13 ∷ []) (lw4 c4 (CX03 ∷ Sw01 ∷ []) (Sw01 ∷ CX13 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sw01 ∷ CS34⁻ ∷ []) (sym (c₂ (Swap) ((CS • CS • CS) ↑))) ▸
       at 3 2 (Sw01 ∷ CX13 ∷ []) (lw4 c4 (CX03 ∷ Sw01 ∷ []) (Sw01 ∷ CX13 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sw01 ∷ CS34 ∷ []) (sym (c₂ (Swap) (CS ↑))) ▸ done

  b26 : Chain (Sw12 ∷ K3 ∷ Sw01 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3 ∷ ι ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ Sw23 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Sw23 ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ CS14 ∷ K3 ∷ ι ∷ Sw01 ∷ Sw12 ∷ [])
  b26 = at 1 2 (Sw01 ∷ K3 ∷ []) (sym (c₂ (Swap) (K ↑))) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (K2 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ K3 ∷ []) (K2 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS24 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS34 ∷ []) (CS24 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 (CS24⁻ ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS34⁻ ∷ []) (CS24⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 8 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b27 : Chain (Sw12 ∷ Sw01 ∷ Sw23 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Sw23 ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ CS14 ∷ K3 ∷ ι ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw34 ∷ K2 ∷ CS23 ∷ Sw34 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ [])
  b27 = at 7 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 (CS14 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS14 ∷ []) (CS14 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (K2 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ K3 ∷ []) (K2 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 3 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (K2 ∷ Sw34 ∷ []) (sym (c₃ (K ↑ ↑) (Swap))) ▸
       at 6 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done

  b28 : Chain (Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw34 ∷ K2 ∷ CS23 ∷ Sw34 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw34 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι ∷ Sw34 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ [])
  b28 = at 6 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 8 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 10 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 10 2 (K2 ∷ Sw34 ∷ []) (sym (c₃ (K ↑ ↑) (Swap))) ▸
       at 11 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸ done

  b29 : Chain (Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw34 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι ∷ Sw34 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ Toff314 ∷ Sw01 ∷ Sw12 ∷ [])
  b29 = at 4 8 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (lw4 c4 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι ∷ []) (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) tt tt Eq.refl) ▸
       at 4 8 (Toff213 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (Toff214 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff314 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CX02 at 1: 2 steps
lem-resp-CX02-at-1 : Complete 4 → ⟪ (CX02 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CX12 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CX02-at-1 c4 = run b0
  where
  b0 : Chain (CX02 ∷ []) (Sw01 ∷ CX12 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Sw01 ∷ CX12 ∷ []) (lw4 c4 (CX02 ∷ Sw01 ∷ []) (Sw01 ∷ CX12 ∷ []) tt tt Eq.refl) ▸ done


-- nat 2 BOX(3;12): 3 steps
lem-nat-2-BOX⟨3·12⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx3-12 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-13 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·12⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-12 ∷ []) (Bx2-13 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ12 ∷ []) (refl) ▸
       at 0 2 (CZ13 ∷ Sw23 ∷ []) (lem-nat-2-CZ12 c4) ▸
       at 0 1 (Bx2-13 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;302): 8 steps
lem-nat-2-BOX⟨1·302⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx1-302 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-203 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·302⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-302 ∷ []) (Bx1-203 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff103 ∷ Bx3-12 ∷ Toff103 ∷ CCZ013 ∷ Bx3-12 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 1 2 (Toff102 ∷ Sw23 ∷ []) (lem-nat-2-TOFF103 c4) ▸
       at 2 2 (Bx2-13 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·12⟩ c4) ▸
       at 3 2 (Toff102 ∷ Sw23 ∷ []) (lem-nat-2-TOFF103 c4) ▸
       at 4 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 5 2 (Bx2-13 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·12⟩ c4) ▸
       at 0 6 (Bx1-203 ∷ []) (refl) ▸ done


-- nat 2 BOX(3;1402): 8 steps
lem-nat-2-BOX⟨3·1402⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx3-1402 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1403 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·1402⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-1402 ∷ []) (Bx2-1403 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff314 ∷ Bx1-302 ∷ Toff314 ∷ CCZ134 ∷ Bx1-302 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 1 2 (Toff214 ∷ Sw23 ∷ []) (lem-nat-2-TOFF314 c4) ▸
       at 2 2 (Bx1-203 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·302⟩ c4) ▸
       at 3 2 (Toff214 ∷ Sw23 ∷ []) (lem-nat-2-TOFF314 c4) ▸
       at 4 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 5 2 (Bx1-203 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·302⟩ c4) ▸
       at 0 6 (Bx2-1403 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;203): 8 steps
lem-nat-2-BOX⟨1·203⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx1-203 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-302 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·203⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-203 ∷ []) (Bx1-302 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff102 ∷ Bx2-13 ∷ Toff102 ∷ CCZ012 ∷ Bx2-13 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 1 2 (Toff103 ∷ Sw23 ∷ []) (lem-nat-2-TOFF102 c4) ▸
       at 2 2 (Bx3-12 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·13⟩ c4) ▸
       at 3 2 (Toff103 ∷ Sw23 ∷ []) (lem-nat-2-TOFF102 c4) ▸
       at 4 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 5 2 (Bx3-12 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·13⟩ c4) ▸
       at 0 6 (Bx1-302 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;1403): 8 steps
lem-nat-2-BOX⟨2·1403⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx2-1403 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1402 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·1403⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-1403 ∷ []) (Bx3-1402 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff214 ∷ Bx1-203 ∷ Toff214 ∷ CCZ124 ∷ Bx1-203 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 1 2 (Toff314 ∷ Sw23 ∷ []) (lem-nat-2-TOFF214 c4) ▸
       at 2 2 (Bx1-302 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·203⟩ c4) ▸
       at 3 2 (Toff314 ∷ Sw23 ∷ []) (lem-nat-2-TOFF214 c4) ▸
       at 4 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 5 2 (Bx1-302 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·203⟩ c4) ▸
       at 0 6 (Bx3-1402 ∷ []) (refl) ▸ done


-- nat 3 BOX(4;12): 2 steps
lem-nat-3-BOX⟨4·12⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx4-12 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-12 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨4·12⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx4-12 ∷ []) (Bx3-12 ∷ Sw34 ∷ [])
  b0 = at 0 2 (Bx4-12 ∷ Sw34 ∷ []) (sym (c₃ (CZ ↑) (Swap))) ▸
       at 0 1 (Bx3-12 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 BOX(1;402): 8 steps
lem-nat-3-BOX⟨1·402⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx1-402 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-302 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨1·402⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx1-402 ∷ []) (Bx1-302 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff104 ∷ Bx4-12 ∷ Toff104 ∷ CCZ014 ∷ Bx4-12 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 1 2 (Toff103 ∷ Sw34 ∷ []) (lem-nat-3-TOFF104 c4) ▸
       at 2 2 (Bx3-12 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·12⟩ c4) ▸
       at 3 2 (Toff103 ∷ Sw34 ∷ []) (lem-nat-3-TOFF104 c4) ▸
       at 4 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 5 2 (Bx3-12 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·12⟩ c4) ▸
       at 0 6 (Bx1-302 ∷ []) (refl) ▸ done


-- nat 3 BOX(4;1302): 8 steps
lem-nat-3-BOX⟨4·1302⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx4-1302 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1402 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨4·1302⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx4-1302 ∷ []) (Bx3-1402 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff413 ∷ Bx1-402 ∷ Toff413 ∷ CCZ134 ∷ Bx1-402 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CCZ134 ∷ []) (CCZ134 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff314 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff413 ∷ []) (Toff314 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx1-302 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·402⟩ c4) ▸
       at 3 2 (Toff314 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff413 ∷ []) (Toff314 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ134 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CCZ134 ∷ []) (CCZ134 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx1-302 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·402⟩ c4) ▸
       at 0 6 (Bx3-1402 ∷ []) (refl) ▸ done


-- nat 3 BOX(3;12): 2 steps
lem-nat-3-BOX⟨3·12⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx3-12 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-12 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨3·12⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx3-12 ∷ []) (Bx4-12 ∷ Sw34 ∷ [])
  b0 = at 0 2 (Bx3-12 ∷ Sw34 ∷ []) (sym (c₃ (CZ ↑) (Swap))) ▸
       at 0 1 (Bx4-12 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 BOX(1;302): 8 steps
lem-nat-3-BOX⟨1·302⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx1-302 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-402 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨1·302⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx1-302 ∷ []) (Bx1-402 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff103 ∷ Bx3-12 ∷ Toff103 ∷ CCZ013 ∷ Bx3-12 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 1 2 (Toff104 ∷ Sw34 ∷ []) (lem-nat-3-TOFF103 c4) ▸
       at 2 2 (Bx4-12 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·12⟩ c4) ▸
       at 3 2 (Toff104 ∷ Sw34 ∷ []) (lem-nat-3-TOFF103 c4) ▸
       at 4 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 5 2 (Bx4-12 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·12⟩ c4) ▸
       at 0 6 (Bx1-402 ∷ []) (refl) ▸ done


-- nat 3 BOX(3;1402): 8 steps
lem-nat-3-BOX⟨3·1402⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx3-1402 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1302 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨3·1402⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx3-1402 ∷ []) (Bx4-1302 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff314 ∷ Bx1-302 ∷ Toff314 ∷ CCZ134 ∷ Bx1-302 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CCZ134 ∷ []) (CCZ134 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff413 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff314 ∷ []) (Toff413 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx1-402 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·302⟩ c4) ▸
       at 3 2 (Toff413 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff314 ∷ []) (Toff413 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ134 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CCZ134 ∷ []) (CCZ134 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx1-402 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·302⟩ c4) ▸
       at 0 6 (Bx4-1302 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;403): 8 steps
lem-nat-2-BOX⟨1·403⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx1-403 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-402 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·403⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-403 ∷ []) (Bx1-402 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff104 ∷ Bx4-13 ∷ Toff104 ∷ CCZ014 ∷ Bx4-13 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 1 2 (Toff104 ∷ Sw23 ∷ []) (lem-nat-2-TOFF104 c4) ▸
       at 2 2 (Bx4-12 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·13⟩ c4) ▸
       at 3 2 (Toff104 ∷ Sw23 ∷ []) (lem-nat-2-TOFF104 c4) ▸
       at 4 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 5 2 (Bx4-12 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·13⟩ c4) ▸
       at 0 6 (Bx1-402 ∷ []) (refl) ▸ done


-- nat 2 BOX(4;1203): 8 steps
lem-nat-2-BOX⟨4·1203⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx4-1203 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1302 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·1203⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-1203 ∷ []) (Bx4-1302 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff412 ∷ Bx1-403 ∷ Toff412 ∷ CCZ124 ∷ Bx1-403 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 1 2 (Toff413 ∷ Sw23 ∷ []) (lem-nat-2-TOFF412 c4) ▸
       at 2 2 (Bx1-402 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·403⟩ c4) ▸
       at 3 2 (Toff413 ∷ Sw23 ∷ []) (lem-nat-2-TOFF412 c4) ▸
       at 4 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 5 2 (Bx1-402 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·403⟩ c4) ▸
       at 0 6 (Bx4-1302 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;402): 8 steps
lem-nat-2-BOX⟨1·402⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx1-402 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-403 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·402⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-402 ∷ []) (Bx1-403 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff104 ∷ Bx4-12 ∷ Toff104 ∷ CCZ014 ∷ Bx4-12 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 1 2 (Toff104 ∷ Sw23 ∷ []) (lem-nat-2-TOFF104 c4) ▸
       at 2 2 (Bx4-13 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·12⟩ c4) ▸
       at 3 2 (Toff104 ∷ Sw23 ∷ []) (lem-nat-2-TOFF104 c4) ▸
       at 4 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 5 2 (Bx4-13 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·12⟩ c4) ▸
       at 0 6 (Bx1-403 ∷ []) (refl) ▸ done


-- nat 2 BOX(4;1302): 8 steps
lem-nat-2-BOX⟨4·1302⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx4-1302 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1203 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·1302⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-1302 ∷ []) (Bx4-1203 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff413 ∷ Bx1-402 ∷ Toff413 ∷ CCZ134 ∷ Bx1-402 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 1 2 (Toff412 ∷ Sw23 ∷ []) (lem-nat-2-TOFF413 c4) ▸
       at 2 2 (Bx1-403 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·402⟩ c4) ▸
       at 3 2 (Toff412 ∷ Sw23 ∷ []) (lem-nat-2-TOFF413 c4) ▸
       at 4 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 5 2 (Bx1-403 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·402⟩ c4) ▸
       at 0 6 (Bx4-1203 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;341): 8 steps
lem-nat-2-BOX⟨2·341⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx2-341 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-241 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·341⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-341 ∷ []) (Bx3-241 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff234 ∷ Bx3-21 ∷ Toff234 ∷ CCZ234 ∷ Bx3-21 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff324 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ Toff234 ∷ []) (Toff324 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx2-31 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·21⟩ c4) ▸
       at 3 2 (Toff324 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ Toff234 ∷ []) (Toff324 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx2-31 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·21⟩ c4) ▸
       at 0 6 (Bx3-241 ∷ []) (refl) ▸ done


-- nat 2 BOX(3;2041): 8 steps
lem-nat-2-BOX⟨3·2041⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx3-2041 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3041 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·2041⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-2041 ∷ []) (Bx2-3041 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff302 ∷ Bx2-341 ∷ Toff302 ∷ CCZ023 ∷ Bx2-341 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff203 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff302 ∷ []) (Toff203 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx3-241 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·341⟩ c4) ▸
       at 3 2 (Toff203 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff302 ∷ []) (Toff203 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx3-241 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·341⟩ c4) ▸
       at 0 6 (Bx2-3041 ∷ []) (refl) ▸ done


-- nat 2 BOX(3;241): 8 steps
lem-nat-2-BOX⟨3·241⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx3-241 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-341 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·241⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-241 ∷ []) (Bx2-341 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff324 ∷ Bx2-31 ∷ Toff324 ∷ CCZ234 ∷ Bx2-31 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ Toff324 ∷ []) (Toff234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx3-21 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·31⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ Toff324 ∷ []) (Toff234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx3-21 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·31⟩ c4) ▸
       at 0 6 (Bx2-341 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;3041): 8 steps
lem-nat-2-BOX⟨2·3041⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx2-3041 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2041 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·3041⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-3041 ∷ []) (Bx3-2041 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff203 ∷ Bx3-241 ∷ Toff203 ∷ CCZ023 ∷ Bx3-241 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff302 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff203 ∷ []) (Toff302 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx2-341 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·241⟩ c4) ▸
       at 3 2 (Toff302 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff203 ∷ []) (Toff302 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx2-341 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·241⟩ c4) ▸
       at 0 6 (Bx3-2041 ∷ []) (refl) ▸ done


-- nat 3 BOX(4;21): 2 steps
lem-nat-3-BOX⟨4·21⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx4-21 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-21 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨4·21⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx4-21 ∷ []) (Bx3-21 ∷ Sw34 ∷ [])
  b0 = at 0 2 (Bx4-21 ∷ Sw34 ∷ []) (sym (c₃ (CZ ↑) (Swap))) ▸
       at 0 1 (Bx3-21 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 BOX(2;431): 8 steps
lem-nat-3-BOX⟨2·431⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx2-431 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-341 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·431⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx2-431 ∷ []) (Bx2-341 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff234 ∷ Bx4-21 ∷ Toff234 ∷ CCZ234 ∷ Bx4-21 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff234 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff234 ∷ []) (Toff234 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx3-21 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·21⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff234 ∷ []) (Toff234 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ234 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx3-21 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·21⟩ c4) ▸
       at 0 6 (Bx2-341 ∷ []) (refl) ▸ done


-- nat 3 BOX(4;2031): 8 steps
lem-nat-3-BOX⟨4·2031⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx4-2031 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2041 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨4·2031⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx4-2031 ∷ []) (Bx3-2041 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff402 ∷ Bx2-431 ∷ Toff402 ∷ CCZ024 ∷ Bx2-431 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 1 2 (Toff302 ∷ Sw34 ∷ []) (lem-nat-3-TOFF402 c4) ▸
       at 2 2 (Bx2-341 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·431⟩ c4) ▸
       at 3 2 (Toff302 ∷ Sw34 ∷ []) (lem-nat-3-TOFF402 c4) ▸
       at 4 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 5 2 (Bx2-341 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·431⟩ c4) ▸
       at 0 6 (Bx3-2041 ∷ []) (refl) ▸ done


-- nat 3 BOX(3;21): 2 steps
lem-nat-3-BOX⟨3·21⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx3-21 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-21 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨3·21⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx3-21 ∷ []) (Bx4-21 ∷ Sw34 ∷ [])
  b0 = at 0 2 (Bx3-21 ∷ Sw34 ∷ []) (sym (c₃ (CZ ↑) (Swap))) ▸
       at 0 1 (Bx4-21 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 BOX(2;341): 8 steps
lem-nat-3-BOX⟨2·341⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx2-341 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-431 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·341⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx2-341 ∷ []) (Bx2-431 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff234 ∷ Bx3-21 ∷ Toff234 ∷ CCZ234 ∷ Bx3-21 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff234 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff234 ∷ []) (Toff234 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx4-21 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·21⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff234 ∷ []) (Toff234 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ234 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx4-21 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·21⟩ c4) ▸
       at 0 6 (Bx2-431 ∷ []) (refl) ▸ done


-- nat 3 BOX(3;2041): 8 steps
lem-nat-3-BOX⟨3·2041⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx3-2041 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2031 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨3·2041⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx3-2041 ∷ []) (Bx4-2031 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff302 ∷ Bx2-341 ∷ Toff302 ∷ CCZ023 ∷ Bx2-341 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4) ▸
       at 1 2 (Toff402 ∷ Sw34 ∷ []) (lem-nat-3-TOFF302 c4) ▸
       at 2 2 (Bx2-431 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·341⟩ c4) ▸
       at 3 2 (Toff402 ∷ Sw34 ∷ []) (lem-nat-3-TOFF302 c4) ▸
       at 4 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4) ▸
       at 5 2 (Bx2-431 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·341⟩ c4) ▸
       at 0 6 (Bx4-2031 ∷ []) (refl) ▸ done


-- nat 3 SBOX(1;0;3;2): 3 steps
lem-nat-3-SBOX⟨1·0·3·2⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb1-0-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-4-2 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨1·0·3·2⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb1-0-3-2 ∷ []) (Sb1-0-4-2 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS03 ∷ []) (refl) ▸
       at 0 2 (CS04 ∷ Sw34 ∷ []) (lem-nat-3-CS03 c4) ▸
       at 0 1 (Sb1-0-4-2 ∷ []) (refl) ▸ done


-- nat 3 SBOXd(1;0;3;2): 3 steps
lem-nat-3-SBOXd⟨1·0·3·2⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb⁻1-0-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-4-2 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨1·0·3·2⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻1-0-3-2 ∷ []) (Sb⁻1-0-4-2 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 2 (CS04⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd03 c4) ▸
       at 0 1 (Sb⁻1-0-4-2 ∷ []) (refl) ▸ done


-- nat 3 SBOX(1;0;42;3): 7 steps
lem-nat-3-SBOX⟨1·0·42·3⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-32-4 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨1·0·42·3⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb1-0-42-3 ∷ []) (Sb1-0-32-4 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (refl) ▸
       at 0 2 (Bx1-0324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·0423⟩ c4) ▸
       at 1 2 (Toff423 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff324 ∷ []) (Toff423 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb1-0-4-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·0·3·2⟩ c4) ▸
       at 3 2 (Toff423 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff324 ∷ []) (Toff423 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sb⁻1-0-4-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨1·0·3·2⟩ c4) ▸
       at 0 5 (Sb1-0-32-4 ∷ []) (refl) ▸ done


-- nat 3 SBOX(1;0;4;2): 3 steps
lem-nat-3-SBOX⟨1·0·4·2⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb1-0-4-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-3-2 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨1·0·4·2⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb1-0-4-2 ∷ []) (Sb1-0-3-2 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS04 ∷ []) (refl) ▸
       at 0 2 (CS03 ∷ Sw34 ∷ []) (lem-nat-3-CS04 c4) ▸
       at 0 1 (Sb1-0-3-2 ∷ []) (refl) ▸ done


-- nat 3 SBOXd(1;0;4;2): 3 steps
lem-nat-3-SBOXd⟨1·0·4·2⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb⁻1-0-4-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-3-2 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨1·0·4·2⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻1-0-4-2 ∷ []) (Sb⁻1-0-3-2 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS04⁻ ∷ []) (refl) ▸
       at 0 2 (CS03⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd04 c4) ▸
       at 0 1 (Sb⁻1-0-3-2 ∷ []) (refl) ▸ done


-- nat 3 SBOX(1;0;32;4): 7 steps
lem-nat-3-SBOX⟨1·0·32·4⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb1-0-32-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨1·0·32·4⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb1-0-32-4 ∷ []) (Sb1-0-42-3 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx1-0324 ∷ Toff423 ∷ Sb1-0-4-2 ∷ Toff423 ∷ Sb⁻1-0-4-2 ∷ []) (refl) ▸
       at 0 2 (Bx1-0423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·0324⟩ c4) ▸
       at 1 2 (Toff324 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff423 ∷ []) (Toff324 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb1-0-3-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·0·4·2⟩ c4) ▸
       at 3 2 (Toff324 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff423 ∷ []) (Toff324 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sb⁻1-0-3-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨1·0·4·2⟩ c4) ▸
       at 0 5 (Sb1-0-42-3 ∷ []) (refl) ▸ done


-- nat 2 SBOX(4;1;2;0): 3 steps
lem-nat-2-SBOX⟨4·1·2·0⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb4-1-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-1-3-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨4·1·2·0⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb4-1-2-0 ∷ []) (Sb4-1-3-0 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS12 ∷ []) (refl) ▸
       at 0 2 (CS13 ∷ Sw23 ∷ []) (lem-nat-2-CS12 c4) ▸
       at 0 1 (Sb4-1-3-0 ∷ []) (refl) ▸ done


-- nat 2 SBOX(4;1;3;0): 3 steps
lem-nat-2-SBOX⟨4·1·3·0⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb4-1-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-1-2-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨4·1·3·0⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb4-1-3-0 ∷ []) (Sb4-1-2-0 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS13 ∷ []) (refl) ▸
       at 0 2 (CS12 ∷ Sw23 ∷ []) (lem-nat-2-CS13 c4) ▸
       at 0 1 (Sb4-1-2-0 ∷ []) (refl) ▸ done


-- nat 3 SBOX(3;1;2;0): 2 steps
lem-nat-3-SBOX⟨3·1·2·0⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb3-1-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-1-2-0 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨3·1·2·0⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb3-1-2-0 ∷ []) (Sb4-1-2-0 ∷ Sw34 ∷ [])
  b0 = at 0 2 (Sb3-1-2-0 ∷ Sw34 ∷ []) (sym (c₃ (CS ↑) (Swap))) ▸
       at 0 1 (Sb4-1-2-0 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 SBOX(4;1;2;0): 2 steps
lem-nat-3-SBOX⟨4·1·2·0⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb4-1-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-1-2-0 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨4·1·2·0⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb4-1-2-0 ∷ []) (Sb3-1-2-0 ∷ Sw34 ∷ [])
  b0 = at 0 2 (Sb4-1-2-0 ∷ Sw34 ∷ []) (sym (c₃ (CS ↑) (Swap))) ▸
       at 0 1 (Sb3-1-2-0 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 SBOX(2;1;3;0): 3 steps
lem-nat-2-SBOX⟨2·1·3·0⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb2-1-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-1-2-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨2·1·3·0⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb2-1-3-0 ∷ []) (Sb3-1-2-0 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS13 ∷ []) (refl) ▸
       at 0 2 (CS12 ∷ Sw23 ∷ []) (lem-nat-2-CS13 c4) ▸
       at 0 1 (Sb3-1-2-0 ∷ []) (refl) ▸ done


-- nat 2 SBOX(3;1;2;0): 3 steps
lem-nat-2-SBOX⟨3·1·2·0⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb3-1-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-3-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨3·1·2·0⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb3-1-2-0 ∷ []) (Sb2-1-3-0 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS12 ∷ []) (refl) ▸
       at 0 2 (CS13 ∷ Sw23 ∷ []) (lem-nat-2-CS12 c4) ▸
       at 0 1 (Sb2-1-3-0 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(4;1;2;0): 3 steps
lem-nat-2-SBOXd⟨4·1·2·0⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb⁻4-1-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-1-3-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨4·1·2·0⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻4-1-2-0 ∷ []) (Sb⁻4-1-3-0 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 2 (CS13⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd12 c4) ▸
       at 0 1 (Sb⁻4-1-3-0 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(4;1;3;0): 3 steps
lem-nat-2-SBOXd⟨4·1·3·0⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb⁻4-1-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-1-2-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨4·1·3·0⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻4-1-3-0 ∷ []) (Sb⁻4-1-2-0 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS13⁻ ∷ []) (refl) ▸
       at 0 2 (CS12⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd13 c4) ▸
       at 0 1 (Sb⁻4-1-2-0 ∷ []) (refl) ▸ done


-- nat 3 SBOXd(3;1;2;0): 2 steps
lem-nat-3-SBOXd⟨3·1·2·0⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb⁻3-1-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-1-2-0 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨3·1·2·0⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻3-1-2-0 ∷ []) (Sb⁻4-1-2-0 ∷ Sw34 ∷ [])
  b0 = at 0 2 (Sb⁻3-1-2-0 ∷ Sw34 ∷ []) (sym (c₃ ((CS • CS • CS) ↑) (Swap))) ▸
       at 0 1 (Sb⁻4-1-2-0 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 SBOXd(4;1;2;0): 2 steps
lem-nat-3-SBOXd⟨4·1·2·0⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb⁻4-1-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-1-2-0 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨4·1·2·0⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻4-1-2-0 ∷ []) (Sb⁻3-1-2-0 ∷ Sw34 ∷ [])
  b0 = at 0 2 (Sb⁻4-1-2-0 ∷ Sw34 ∷ []) (sym (c₃ ((CS • CS • CS) ↑) (Swap))) ▸
       at 0 1 (Sb⁻3-1-2-0 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 SBOXd(2;1;3;0): 3 steps
lem-nat-2-SBOXd⟨2·1·3·0⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb⁻2-1-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-1-2-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨2·1·3·0⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻2-1-3-0 ∷ []) (Sb⁻3-1-2-0 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS13⁻ ∷ []) (refl) ▸
       at 0 2 (CS12⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd13 c4) ▸
       at 0 1 (Sb⁻3-1-2-0 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(3;1;2;0): 3 steps
lem-nat-2-SBOXd⟨3·1·2·0⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb⁻3-1-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-1-3-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨3·1·2·0⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻3-1-2-0 ∷ []) (Sb⁻2-1-3-0 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 2 (CS13⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd12 c4) ▸
       at 0 1 (Sb⁻2-1-3-0 ∷ []) (refl) ▸ done


-- nat 2 SBOX(2;0;1;3): 2 steps
lem-nat-2-SBOX⟨2·0·1·3⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb2-0-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-1-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨2·0·1·3⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb2-0-1-3 ∷ []) (Sb3-0-1-2 ∷ Sw23 ∷ [])
  b0 = at 0 2 (Sb2-0-1-3 ∷ Sw23 ∷ []) (sym (c₂ (CS) (Swap))) ▸
       at 0 1 (Sb3-0-1-2 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 SBOXd(2;0;1;3): 2 steps
lem-nat-2-SBOXd⟨2·0·1·3⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb⁻2-0-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-0-1-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨2·0·1·3⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻2-0-1-3 ∷ []) (Sb⁻3-0-1-2 ∷ Sw23 ∷ [])
  b0 = at 0 2 (Sb⁻2-0-1-3 ∷ Sw23 ∷ []) (sym (c₂ (CS • CS • CS) (Swap))) ▸
       at 0 1 (Sb⁻3-0-1-2 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 SBOX(2;0;43;1): 7 steps
lem-nat-2-SBOX⟨2·0·43·1⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb2-0-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-42-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨2·0·43·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb2-0-43-1 ∷ []) (Sb3-0-42-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx2-0431 ∷ Toff134 ∷ Sb2-0-1-3 ∷ Toff134 ∷ Sb⁻2-0-1-3 ∷ []) (refl) ▸
       at 0 2 (Bx3-0421 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0431⟩ c4) ▸
       at 1 2 (Toff124 ∷ Sw23 ∷ []) (lem-nat-2-TOFF134 c4) ▸
       at 2 2 (Sb3-0-1-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·0·1·3⟩ c4) ▸
       at 3 2 (Toff124 ∷ Sw23 ∷ []) (lem-nat-2-TOFF134 c4) ▸
       at 4 2 (Sb⁻3-0-1-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨2·0·1·3⟩ c4) ▸
       at 0 5 (Sb3-0-42-1 ∷ []) (refl) ▸ done


-- nat 0 BOX(4;021): 8 steps
lem-nat-0-BOX⟨4·021⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx4-021 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-120 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·021⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-021 ∷ []) (Bx4-120 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff402 ∷ Bx0-41 ∷ Toff402 ∷ CCZ024 ∷ Bx0-41 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 1 2 (Toff412 ∷ Sw01 ∷ []) (lem-nat-0-TOFF402 c4) ▸
       at 2 2 (Bx1-40 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·41⟩ c4) ▸
       at 3 2 (Toff412 ∷ Sw01 ∷ []) (lem-nat-0-TOFF402 c4) ▸
       at 4 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 5 2 (Bx1-40 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·41⟩ c4) ▸
       at 0 6 (Bx4-120 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;4321): 8 steps
lem-nat-0-BOX⟨0·4321⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx0-4321 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-4320 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·4321⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-4321 ∷ []) (Bx1-4320 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff034 ∷ Bx4-021 ∷ Toff034 ∷ CCZ034 ∷ Bx4-021 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 1 2 (Toff134 ∷ Sw01 ∷ []) (lem-nat-0-TOFF034 c4) ▸
       at 2 2 (Bx4-120 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·021⟩ c4) ▸
       at 3 2 (Toff134 ∷ Sw01 ∷ []) (lem-nat-0-TOFF034 c4) ▸
       at 4 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 5 2 (Bx4-120 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·021⟩ c4) ▸
       at 0 6 (Bx1-4320 ∷ []) (refl) ▸ done


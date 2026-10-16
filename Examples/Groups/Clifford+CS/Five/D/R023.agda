{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R023 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-CCZ023 ; lem-nat-1-CCZ034 ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ013 ; lem-nat-2-CCZ024 ; lem-nat-2-CCZ034 ; lem-nat-2-TOFF012 ; lem-nat-2-TOFF024 ; lem-nat-2-TOFF034 ; lem-nat-2-TOFF301 ; lem-nat-3-CCZ024)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-1-CCZ013 ; lem-nat-2-TOFF201 ; lem-nat-3-CCZ023)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-1-TOFF301 ; lem-nat-1-TOFF302 ; lem-nat-3-TOFF203)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-3-CZ23)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-2-TOFF104)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-3-CCZ123 ; lem-nat-3-CCZ124)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-nat-1-CZ01 ; lem-nat-2-CCZ014 ; lem-nat-3-CZ24)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-nat-1-CS01 ; lem-nat-1-CS02)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-1-BOX⟨3·02⟩ ; lem-nat-1-CSd02 ; lem-nat-2-BOX⟨3·01⟩)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-1-CSd01 ; lem-nat-1-TOFF034 ; lem-nat-2-TOFF124)
open import Examples.Groups.Clifford+CS.Five.D.R017 using (lem-nat-3-TOFF024)
open import Examples.Groups.Clifford+CS.Five.D.R019 using (lem-nat-1-BOX⟨1·34⟩ ; lem-nat-1-BOX⟨2·34⟩ ; lem-nat-2-BOX⟨1·03⟩)
open import Examples.Groups.Clifford+CS.Five.D.R020 using (lem-nat-3-TOFF123 ; lem-nat-3-TOFF124)
open import Examples.Groups.Clifford+CS.Five.D.R021 using (lem-nat-1-BOX⟨1·0432⟩)
open import Examples.Groups.Clifford+CS.Five.D.R022 using (lem-nat-1-BOX⟨2·0431⟩ ; lem-nat-2-SBOX⟨1·0·3·2⟩ ; lem-nat-2-SBOXd⟨1·0·3·2⟩)
-- comm TOFF203 CX41: 181 steps
lem-comm-TOFF203-CX41 : Complete 4 → ⟪ (Toff203 ∷ CX41 ∷ []) ⟫ʷ ≈ ⟪ (CX41 ∷ Toff203 ∷ []) ⟫ʷ
lem-comm-TOFF203-CX41 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (run b22))))))))))))))))))))))
  where
  b0 : Chain (Toff203 ∷ CX41 ∷ []) (Sw12 ∷ K1 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 1 (Sw12 ∷ Toff103 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸ done

  b1 : Chain (Sw12 ∷ K1 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw34 ∷ []) (Sw12 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw34 ∷ [])
  b1 = at 6 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 9 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done

  b2 : Chain (Sw12 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw34 ∷ []) (K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw12 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw34 ∷ [])
  b2 = at 0 2 (K2 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ K1 ∷ []) (K2 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS23 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS13 ∷ []) (CS23 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS23⁻ ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS13⁻ ∷ []) (CS23⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS03 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS03 ∷ []) (CS03 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸ done

  b3 : Chain (K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw12 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw34 ∷ []) (K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw34 ∷ CX02 ∷ CS04 ∷ K2 ∷ ι ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw34 ∷ [])
  b3 = at 6 2 (K2 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ K1 ∷ []) (K2 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 8 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 (Sw34 ∷ ι ∷ []) (c₁ (iI) (Swap ↑ ↑)) ▸
       at 6 2 (Sw34 ∷ K2 ∷ []) (c₃ (K ↑ ↑) (Swap)) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw34 ∷ CX02 ∷ []) (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap)) ▸ done

  b4 : Chain (K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw34 ∷ CX02 ∷ CS04 ∷ K2 ∷ ι ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw12 ∷ K1 ∷ Sw12 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K2 ∷ ι ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw34 ∷ [])
  b4 = at 3 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw34 ∷ CX02 ∷ []) (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap)) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (CS24 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw34 ∷ K2 ∷ []) (c₃ (K ↑ ↑) (Swap)) ▸
       at 1 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (K1 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ K2 ∷ []) (K1 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸ done

  b5 : Chain (Sw34 ∷ Sw12 ∷ K1 ∷ Sw12 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K2 ∷ ι ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ Sw12 ∷ CS03 ∷ Sw34 ∷ K2 ∷ ι ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw34 ∷ [])
  b5 = at 3 2 (CS14 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS24 ∷ []) (CS14 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 (CS14⁻ ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS24⁻ ∷ []) (CS14⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸
       at 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸ done

  b6 : Chain (Sw34 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ Sw12 ∷ CS03 ∷ Sw34 ∷ K2 ∷ ι ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ Sw34 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw34 ∷ [])
  b6 = at 8 2 (CS03 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS03 ∷ []) (CS03 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 7 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K1 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ K2 ∷ []) (K1 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 5 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b7 : Chain (Sw34 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ Sw34 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ Sw34 ∷ ι ∷ Sw12 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw34 ∷ [])
  b7 = at 4 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 9 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 9 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸ done

  b8 : Chain (Sw34 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ Sw34 ∷ ι ∷ Sw12 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw34 ∷ [])
  b8 = at 10 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done

  b9 : Chain (Sw34 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw12 ∷ Toff104 ∷ Sw12 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw34 ∷ [])
  b9 = at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 10 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 11 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 4 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (Toff103 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff104 ∷ []) (by-assoc Eq.refl) ▸ done

  b10 : Chain (Sw34 ∷ Sw12 ∷ Toff104 ∷ Sw12 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ CX32 ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ [])
  b10 = at 1 3 (Toff204 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (Toff304 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 10 3 (CX31 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CX32 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CX31 ∷ []) (CX32 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 10 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸ done

  b11 : Chain (Sw34 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ CX32 ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ [])
  b11 = at 8 3 (CX42 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX43 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CX42 ∷ []) (CX43 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CX43 ∷ Toff102 ∷ []) (c₃ (K ↑ • CCZ • K ↑ • iI) (CX₁₀)) ▸
       at 5 2 (CX42 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CX43 ∷ []) (CX42 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Sw34 ∷ CX32 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 (CX31 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CX32 ∷ []) (CX31 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b12 : Chain (Sw34 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ [])
  b12 = at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 3 9 (Toff304 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw23 ∷ Toff204 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 4 1 (Sw12 ∷ Toff104 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (Sw34 ∷ Toff103 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸ done

  b13 : Chain (Sw34 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ []) (Sw34 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ [])
  b13 = at 6 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 7 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 9 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 13 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸ done

  b14 : Chain (Sw34 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ []) (Sw34 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ Sw34 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ [])
  b14 = at 11 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 13 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 14 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸ done

  b15 : Chain (Sw34 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ Sw34 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ []) (Sw34 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw34 ∷ [])
  b15 = at 10 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 8 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 12 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 10 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 12 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 13 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done

  b16 : Chain (Sw34 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw34 ∷ []) (Sw34 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw12 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw34 ∷ [])
  b16 = at 4 2 (K2 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ K1 ∷ []) (K2 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CS24 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS14 ∷ []) (CS24 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 8 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CS24⁻ ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS14⁻ ∷ []) (CS24⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 10 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 8 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 10 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b17 : Chain (Sw34 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw12 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw34 ∷ []) (Sw34 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K2 ∷ Sw34 ∷ ι ∷ [])
  b17 = at 9 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 10 2 (CS03 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS03 ∷ []) (CS03 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 9 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (K2 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ K1 ∷ []) (K2 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 12 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸
       at 11 2 (Sw34 ∷ ι ∷ []) (c₁ (iI) (Swap ↑ ↑)) ▸ done

  b18 : Chain (Sw34 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K2 ∷ Sw34 ∷ ι ∷ []) (Sw34 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ K2 ∷ Sw34 ∷ CS23 ∷ Sw34 ∷ Sw34 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ [])
  b18 = at 10 2 (Sw34 ∷ K2 ∷ []) (c₃ (K ↑ ↑) (Swap)) ▸
       at 9 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 (Sw34 ∷ CX02 ∷ []) (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap)) ▸
       at 7 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 (Sw34 ∷ CX02 ∷ []) (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap)) ▸
       at 5 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b19 : Chain (Sw34 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ K2 ∷ Sw34 ∷ CS23 ∷ Sw34 ∷ Sw34 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ []) (Sw34 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw12 ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ [])
  b19 = at 7 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 4 2 (Sw34 ∷ K2 ∷ []) (c₃ (K ↑ ↑) (Swap)) ▸
       at 5 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (K1 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ K2 ∷ []) (K1 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CS13 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS23 ∷ []) (CS13 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 9 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸
       at 9 2 (CS13⁻ ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS23⁻ ∷ []) (CS13⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸ done

  b20 : Chain (Sw34 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw12 ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ []) (Sw34 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ K1 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw12 ∷ [])
  b20 = at 11 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸
       at 11 2 (CS03 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS03 ∷ []) (CS03 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (K1 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ K2 ∷ []) (K1 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 13 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b21 : Chain (Sw34 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ K1 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw12 ∷ []) (Sw34 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ Sw23 ∷ ι ∷ Sw12 ∷ [])
  b21 = at 8 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 11 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 11 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 13 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸ done

  b22 : Chain (Sw34 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ Sw23 ∷ ι ∷ Sw12 ∷ []) (CX41 ∷ Toff203 ∷ [])
  b22 = at 14 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 7 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 6 3 (Toff103 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (Toff203 ∷ []) (by-assoc Eq.refl) ▸
       at 0 5 (CX41 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CZ13 at 2: 4 steps
lem-resp-CZ13-at-2 : Complete 4 → ⟪ (CZ13 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CZ23 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CZ13-at-2 c4 = run b0
  where
  b0 : Chain (CZ13 ∷ []) (Sw12 ∷ Sw01 ∷ CZ23 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Sw12 ∷ CZ23 ∷ []) (lw4 c4 (CZ13 ∷ Sw12 ∷ []) (Sw12 ∷ CZ23 ∷ []) tt tt Eq.refl) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sw01 ∷ CZ23 ∷ []) (sym (c₂ (Swap) (CZ))) ▸ done


-- nat 1 BOX(3;01): 3 steps
lem-nat-1-BOX⟨3·01⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx3-01 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-02 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·01⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-01 ∷ []) (Bx3-02 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ01 ∷ []) (refl) ▸
       at 0 2 (CZ02 ∷ Sw12 ∷ []) (lem-nat-1-CZ01 c4) ▸
       at 0 1 (Bx3-02 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;341): 8 steps
lem-nat-1-BOX⟨0·341⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx0-341 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-342 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·341⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-341 ∷ []) (Bx0-342 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff034 ∷ Bx3-01 ∷ Toff034 ∷ CCZ034 ∷ Bx3-01 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 1 2 (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 c4) ▸
       at 2 2 (Bx3-02 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·01⟩ c4) ▸
       at 3 2 (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 c4) ▸
       at 4 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 5 2 (Bx3-02 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·01⟩ c4) ▸
       at 0 6 (Bx0-342 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;0241): 8 steps
lem-nat-1-BOX⟨3·0241⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx3-0241 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0142 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·0241⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-0241 ∷ []) (Bx3-0142 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff302 ∷ Bx0-341 ∷ Toff302 ∷ CCZ023 ∷ Bx0-341 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 1 2 (Toff301 ∷ Sw12 ∷ []) (lem-nat-1-TOFF302 c4) ▸
       at 2 2 (Bx0-342 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·341⟩ c4) ▸
       at 3 2 (Toff301 ∷ Sw12 ∷ []) (lem-nat-1-TOFF302 c4) ▸
       at 4 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 5 2 (Bx0-342 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·341⟩ c4) ▸
       at 0 6 (Bx3-0142 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;342): 8 steps
lem-nat-1-BOX⟨0·342⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx0-342 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-341 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·342⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-342 ∷ []) (Bx0-341 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff034 ∷ Bx3-02 ∷ Toff034 ∷ CCZ034 ∷ Bx3-02 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 1 2 (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 c4) ▸
       at 2 2 (Bx3-01 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·02⟩ c4) ▸
       at 3 2 (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 c4) ▸
       at 4 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 5 2 (Bx3-01 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·02⟩ c4) ▸
       at 0 6 (Bx0-341 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;0142): 8 steps
lem-nat-1-BOX⟨3·0142⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx3-0142 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0241 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·0142⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-0142 ∷ []) (Bx3-0241 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff301 ∷ Bx0-342 ∷ Toff301 ∷ CCZ013 ∷ Bx0-342 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 1 2 (Toff302 ∷ Sw12 ∷ []) (lem-nat-1-TOFF301 c4) ▸
       at 2 2 (Bx0-341 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·342⟩ c4) ▸
       at 3 2 (Toff302 ∷ Sw12 ∷ []) (lem-nat-1-TOFF301 c4) ▸
       at 4 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 5 2 (Bx0-341 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·342⟩ c4) ▸
       at 0 6 (Bx3-0241 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;01): 2 steps
lem-nat-2-BOX⟨2·01⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx2-01 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-01 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·01⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-01 ∷ []) (Bx3-01 ∷ Sw23 ∷ [])
  b0 = at 0 2 (Bx2-01 ∷ Sw23 ∷ []) (sym (c₂ (CZ) (Swap))) ▸
       at 0 1 (Bx3-01 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 BOX(0;241): 8 steps
lem-nat-2-BOX⟨0·241⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx0-241 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-341 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·241⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-241 ∷ []) (Bx0-341 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx2-01 ∷ Toff024 ∷ CCZ024 ∷ Bx2-01 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 1 2 (Toff034 ∷ Sw23 ∷ []) (lem-nat-2-TOFF024 c4) ▸
       at 2 2 (Bx3-01 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·01⟩ c4) ▸
       at 3 2 (Toff034 ∷ Sw23 ∷ []) (lem-nat-2-TOFF024 c4) ▸
       at 4 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 5 2 (Bx3-01 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·01⟩ c4) ▸
       at 0 6 (Bx0-341 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;0341): 8 steps
lem-nat-2-BOX⟨2·0341⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx2-0341 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0241 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·0341⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-0341 ∷ []) (Bx3-0241 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff203 ∷ Bx0-241 ∷ Toff203 ∷ CCZ023 ∷ Bx0-241 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff302 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff203 ∷ []) (Toff302 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-341 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·241⟩ c4) ▸
       at 3 2 (Toff302 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff203 ∷ []) (Toff302 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx0-341 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·241⟩ c4) ▸
       at 0 6 (Bx3-0241 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;341): 8 steps
lem-nat-2-BOX⟨0·341⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx0-341 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-241 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·341⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-341 ∷ []) (Bx0-241 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff034 ∷ Bx3-01 ∷ Toff034 ∷ CCZ034 ∷ Bx3-01 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 1 2 (Toff024 ∷ Sw23 ∷ []) (lem-nat-2-TOFF034 c4) ▸
       at 2 2 (Bx2-01 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·01⟩ c4) ▸
       at 3 2 (Toff024 ∷ Sw23 ∷ []) (lem-nat-2-TOFF034 c4) ▸
       at 4 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 5 2 (Bx2-01 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·01⟩ c4) ▸
       at 0 6 (Bx0-241 ∷ []) (refl) ▸ done


-- nat 2 BOX(3;0241): 8 steps
lem-nat-2-BOX⟨3·0241⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx3-0241 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0341 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·0241⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-0241 ∷ []) (Bx2-0341 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff302 ∷ Bx0-341 ∷ Toff302 ∷ CCZ023 ∷ Bx0-341 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff203 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff302 ∷ []) (Toff203 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-241 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·341⟩ c4) ▸
       at 3 2 (Toff203 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff302 ∷ []) (Toff203 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx0-241 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·341⟩ c4) ▸
       at 0 6 (Bx2-0341 ∷ []) (refl) ▸ done


-- nat 3 BOX(0;241): 8 steps
lem-nat-3-BOX⟨0·241⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx0-241 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-231 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·241⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx0-241 ∷ []) (Bx0-231 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx2-01 ∷ Toff024 ∷ CCZ024 ∷ Bx2-01 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 1 2 (Toff023 ∷ Sw34 ∷ []) (lem-nat-3-TOFF024 c4) ▸
       at 2 2 (Bx2-01 ∷ Sw34 ∷ []) (sym (c₂ (CZ) (Swap ↑))) ▸
       at 3 2 (Toff023 ∷ Sw34 ∷ []) (lem-nat-3-TOFF024 c4) ▸
       at 4 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 5 2 (Bx2-01 ∷ Sw34 ∷ []) (sym (c₂ (CZ) (Swap ↑))) ▸
       at 0 6 (Bx0-231 ∷ []) (refl) ▸ done


-- nat 3 BOX(2;0341): 8 steps
lem-nat-3-BOX⟨2·0341⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx2-0341 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0431 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·0341⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx2-0341 ∷ []) (Bx2-0431 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff203 ∷ Bx0-241 ∷ Toff203 ∷ CCZ023 ∷ Bx0-241 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4) ▸
       at 1 2 (Toff204 ∷ Sw34 ∷ []) (lem-nat-3-TOFF203 c4) ▸
       at 2 2 (Bx0-231 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·241⟩ c4) ▸
       at 3 2 (Toff204 ∷ Sw34 ∷ []) (lem-nat-3-TOFF203 c4) ▸
       at 4 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4) ▸
       at 5 2 (Bx0-231 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·241⟩ c4) ▸
       at 0 6 (Bx2-0431 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;123): 8 steps
lem-nat-2-BOX⟨0·123⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx0-123 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-132 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·123⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-123 ∷ []) (Bx0-132 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ Bx1-03 ∷ Toff012 ∷ CCZ012 ∷ Bx1-03 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 1 2 (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 c4) ▸
       at 2 2 (Bx1-02 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·03⟩ c4) ▸
       at 3 2 (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 c4) ▸
       at 4 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 5 2 (Bx1-02 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·03⟩ c4) ▸
       at 0 6 (Bx0-132 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;0423): 8 steps
lem-nat-2-BOX⟨1·0423⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0432 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·0423⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-0423 ∷ []) (Bx1-0432 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff104 ∷ Bx0-123 ∷ Toff104 ∷ CCZ014 ∷ Bx0-123 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 1 2 (Toff104 ∷ Sw23 ∷ []) (lem-nat-2-TOFF104 c4) ▸
       at 2 2 (Bx0-132 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·123⟩ c4) ▸
       at 3 2 (Toff104 ∷ Sw23 ∷ []) (lem-nat-2-TOFF104 c4) ▸
       at 4 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 5 2 (Bx0-132 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·123⟩ c4) ▸
       at 0 6 (Bx1-0432 ∷ []) (refl) ▸ done


-- nat 1 SBOX(3;0;1;4): 3 steps
lem-nat-1-SBOX⟨3·0·1·4⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb3-0-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-2-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨3·0·1·4⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb3-0-1-4 ∷ []) (Sb3-0-2-4 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS01 ∷ []) (refl) ▸
       at 0 2 (CS02 ∷ Sw12 ∷ []) (lem-nat-1-CS01 c4) ▸
       at 0 1 (Sb3-0-2-4 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(3;0;1;4): 3 steps
lem-nat-1-SBOXd⟨3·0·1·4⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb⁻3-0-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-0-2-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨3·0·1·4⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻3-0-1-4 ∷ []) (Sb⁻3-0-2-4 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS01⁻ ∷ []) (refl) ▸
       at 0 2 (CS02⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd01 c4) ▸
       at 0 1 (Sb⁻3-0-2-4 ∷ []) (refl) ▸ done


-- nat 1 SBOX(3;0;24;1): 7 steps
lem-nat-1-SBOX⟨3·0·24·1⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb3-0-24-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-14-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨3·0·24·1⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb3-0-24-1 ∷ []) (Sb3-0-14-2 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx3-0241 ∷ Toff124 ∷ Sb3-0-1-4 ∷ Toff124 ∷ Sb⁻3-0-1-4 ∷ []) (refl) ▸
       at 0 2 (Bx3-0142 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0241⟩ c4) ▸
       at 1 2 (Toff214 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff124 ∷ []) (Toff214 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb3-0-2-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·1·4⟩ c4) ▸
       at 3 2 (Toff214 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff124 ∷ []) (Toff214 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sb⁻3-0-2-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨3·0·1·4⟩ c4) ▸
       at 0 5 (Sb3-0-14-2 ∷ []) (refl) ▸ done


-- nat 1 SBOX(3;0;2;4): 3 steps
lem-nat-1-SBOX⟨3·0·2·4⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb3-0-2-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-1-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨3·0·2·4⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb3-0-2-4 ∷ []) (Sb3-0-1-4 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS02 ∷ []) (refl) ▸
       at 0 2 (CS01 ∷ Sw12 ∷ []) (lem-nat-1-CS02 c4) ▸
       at 0 1 (Sb3-0-1-4 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(3;0;2;4): 3 steps
lem-nat-1-SBOXd⟨3·0·2·4⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb⁻3-0-2-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-0-1-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨3·0·2·4⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻3-0-2-4 ∷ []) (Sb⁻3-0-1-4 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS02⁻ ∷ []) (refl) ▸
       at 0 2 (CS01⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd02 c4) ▸
       at 0 1 (Sb⁻3-0-1-4 ∷ []) (refl) ▸ done


-- nat 1 SBOX(3;0;14;2): 7 steps
lem-nat-1-SBOX⟨3·0·14·2⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb3-0-14-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-24-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨3·0·14·2⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb3-0-14-2 ∷ []) (Sb3-0-24-1 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx3-0142 ∷ Toff214 ∷ Sb3-0-2-4 ∷ Toff214 ∷ Sb⁻3-0-2-4 ∷ []) (refl) ▸
       at 0 2 (Bx3-0241 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0142⟩ c4) ▸
       at 1 2 (Toff124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff214 ∷ []) (Toff124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb3-0-1-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·2·4⟩ c4) ▸
       at 3 2 (Toff124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff214 ∷ []) (Toff124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sb⁻3-0-1-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨3·0·2·4⟩ c4) ▸
       at 0 5 (Sb3-0-24-1 ∷ []) (refl) ▸ done


-- nat 2 TOFF134: 2 steps
lem-nat-2-TOFF134 : Complete 4 → ⟪ (Sw23 ∷ Toff134 ∷ []) ⟫ʷ ≈ ⟪ (Toff124 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-TOFF134 c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Toff134 ∷ []) (Toff124 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Toff124 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- nat 2 SBOX(2;0;1;4): 2 steps
lem-nat-2-SBOX⟨2·0·1·4⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb2-0-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-1-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨2·0·1·4⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb2-0-1-4 ∷ []) (Sb3-0-1-4 ∷ Sw23 ∷ [])
  b0 = at 0 2 (Sb2-0-1-4 ∷ Sw23 ∷ []) (sym (c₂ (CS) (Swap))) ▸
       at 0 1 (Sb3-0-1-4 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 SBOXd(2;0;1;4): 2 steps
lem-nat-2-SBOXd⟨2·0·1·4⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb⁻2-0-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-0-1-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨2·0·1·4⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻2-0-1-4 ∷ []) (Sb⁻3-0-1-4 ∷ Sw23 ∷ [])
  b0 = at 0 2 (Sb⁻2-0-1-4 ∷ Sw23 ∷ []) (sym (c₂ (CS • CS • CS) (Swap))) ▸
       at 0 1 (Sb⁻3-0-1-4 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 SBOX(2;0;34;1): 7 steps
lem-nat-2-SBOX⟨2·0·34·1⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb2-0-34-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-24-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨2·0·34·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb2-0-34-1 ∷ []) (Sb3-0-24-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx2-0341 ∷ Toff134 ∷ Sb2-0-1-4 ∷ Toff134 ∷ Sb⁻2-0-1-4 ∷ []) (refl) ▸
       at 0 2 (Bx3-0241 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0341⟩ c4) ▸
       at 1 2 (Toff124 ∷ Sw23 ∷ []) (lem-nat-2-TOFF134 c4) ▸
       at 2 2 (Sb3-0-1-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·0·1·4⟩ c4) ▸
       at 3 2 (Toff124 ∷ Sw23 ∷ []) (lem-nat-2-TOFF134 c4) ▸
       at 4 2 (Sb⁻3-0-1-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨2·0·1·4⟩ c4) ▸
       at 0 5 (Sb3-0-24-1 ∷ []) (refl) ▸ done


-- nat 2 SBOX(3;0;1;4): 2 steps
lem-nat-2-SBOX⟨3·0·1·4⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb3-0-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-1-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨3·0·1·4⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb3-0-1-4 ∷ []) (Sb2-0-1-4 ∷ Sw23 ∷ [])
  b0 = at 0 2 (Sb3-0-1-4 ∷ Sw23 ∷ []) (sym (c₂ (CS) (Swap))) ▸
       at 0 1 (Sb2-0-1-4 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 SBOXd(3;0;1;4): 2 steps
lem-nat-2-SBOXd⟨3·0·1·4⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb⁻3-0-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-1-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨3·0·1·4⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻3-0-1-4 ∷ []) (Sb⁻2-0-1-4 ∷ Sw23 ∷ [])
  b0 = at 0 2 (Sb⁻3-0-1-4 ∷ Sw23 ∷ []) (sym (c₂ (CS • CS • CS) (Swap))) ▸
       at 0 1 (Sb⁻2-0-1-4 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 SBOX(3;0;24;1): 7 steps
lem-nat-2-SBOX⟨3·0·24·1⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb3-0-24-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-34-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨3·0·24·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb3-0-24-1 ∷ []) (Sb2-0-34-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx3-0241 ∷ Toff124 ∷ Sb3-0-1-4 ∷ Toff124 ∷ Sb⁻3-0-1-4 ∷ []) (refl) ▸
       at 0 2 (Bx2-0341 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0241⟩ c4) ▸
       at 1 2 (Toff134 ∷ Sw23 ∷ []) (lem-nat-2-TOFF124 c4) ▸
       at 2 2 (Sb2-0-1-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·1·4⟩ c4) ▸
       at 3 2 (Toff134 ∷ Sw23 ∷ []) (lem-nat-2-TOFF124 c4) ▸
       at 4 2 (Sb⁻2-0-1-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨3·0·1·4⟩ c4) ▸
       at 0 5 (Sb2-0-34-1 ∷ []) (refl) ▸ done


-- nat 3 SBOX(2;0;1;4): 2 steps
lem-nat-3-SBOX⟨2·0·1·4⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb2-0-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-1-3 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨2·0·1·4⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb2-0-1-4 ∷ []) (Sb2-0-1-3 ∷ Sw34 ∷ [])
  b0 = at 0 2 (Sb2-0-1-4 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 0 1 (Sb2-0-1-3 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 SBOXd(2;0;1;4): 2 steps
lem-nat-3-SBOXd⟨2·0·1·4⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb⁻2-0-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-1-3 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨2·0·1·4⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻2-0-1-4 ∷ []) (Sb⁻2-0-1-3 ∷ Sw34 ∷ [])
  b0 = at 0 2 (Sb⁻2-0-1-4 ∷ Sw34 ∷ []) (sym (c₂ (CS • CS • CS) (Swap ↑))) ▸
       at 0 1 (Sb⁻2-0-1-3 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 SBOX(2;0;34;1): 7 steps
lem-nat-3-SBOX⟨2·0·34·1⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb2-0-34-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-43-1 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨2·0·34·1⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb2-0-34-1 ∷ []) (Sb2-0-43-1 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx2-0341 ∷ Toff134 ∷ Sb2-0-1-4 ∷ Toff134 ∷ Sb⁻2-0-1-4 ∷ []) (refl) ▸
       at 0 2 (Bx2-0431 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·0341⟩ c4) ▸
       at 1 2 (Toff134 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff134 ∷ []) (Toff134 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb2-0-1-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·0·1·4⟩ c4) ▸
       at 3 2 (Toff134 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff134 ∷ []) (Toff134 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sb⁻2-0-1-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨2·0·1·4⟩ c4) ▸
       at 0 5 (Sb2-0-43-1 ∷ []) (refl) ▸ done


-- nat 1 SBOX(1;0;2;3): 3 steps
lem-nat-1-SBOX⟨1·0·2·3⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb1-0-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-1-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨1·0·2·3⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb1-0-2-3 ∷ []) (Sb2-0-1-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS02 ∷ []) (refl) ▸
       at 0 2 (CS01 ∷ Sw12 ∷ []) (lem-nat-1-CS02 c4) ▸
       at 0 1 (Sb2-0-1-3 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(1;0;2;3): 3 steps
lem-nat-1-SBOXd⟨1·0·2·3⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb⁻1-0-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-1-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨1·0·2·3⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻1-0-2-3 ∷ []) (Sb⁻2-0-1-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS02⁻ ∷ []) (refl) ▸
       at 0 2 (CS01⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd02 c4) ▸
       at 0 1 (Sb⁻2-0-1-3 ∷ []) (refl) ▸ done


-- nat 1 SBOX(1;0;43;2): 7 steps
lem-nat-1-SBOX⟨1·0·43·2⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-43-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨1·0·43·2⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb1-0-43-2 ∷ []) (Sb2-0-43-1 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 0 2 (Bx2-0431 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0432⟩ c4) ▸
       at 1 2 (Toff134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff234 ∷ []) (Toff134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb2-0-1-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·2·3⟩ c4) ▸
       at 3 2 (Toff134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff234 ∷ []) (Toff134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sb⁻2-0-1-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·0·2·3⟩ c4) ▸
       at 0 5 (Sb2-0-43-1 ∷ []) (refl) ▸ done


-- nat 1 SBOX(2;0;1;3): 3 steps
lem-nat-1-SBOX⟨2·0·1·3⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb2-0-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-2-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨2·0·1·3⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb2-0-1-3 ∷ []) (Sb1-0-2-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS01 ∷ []) (refl) ▸
       at 0 2 (CS02 ∷ Sw12 ∷ []) (lem-nat-1-CS01 c4) ▸
       at 0 1 (Sb1-0-2-3 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(2;0;1;3): 3 steps
lem-nat-1-SBOXd⟨2·0·1·3⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb⁻2-0-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-2-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨2·0·1·3⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻2-0-1-3 ∷ []) (Sb⁻1-0-2-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS01⁻ ∷ []) (refl) ▸
       at 0 2 (CS02⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd01 c4) ▸
       at 0 1 (Sb⁻1-0-2-3 ∷ []) (refl) ▸ done


-- nat 1 SBOX(2;0;43;1): 7 steps
lem-nat-1-SBOX⟨2·0·43·1⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb2-0-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-43-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨2·0·43·1⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb2-0-43-1 ∷ []) (Sb1-0-43-2 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx2-0431 ∷ Toff134 ∷ Sb2-0-1-3 ∷ Toff134 ∷ Sb⁻2-0-1-3 ∷ []) (refl) ▸
       at 0 2 (Bx1-0432 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0431⟩ c4) ▸
       at 1 2 (Toff234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff134 ∷ []) (Toff234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb1-0-2-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·1·3⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff134 ∷ []) (Toff234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sb⁻1-0-2-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·1·3⟩ c4) ▸
       at 0 5 (Sb1-0-43-2 ∷ []) (refl) ▸ done


-- nat 2 SBOX(1;0;42;3): 7 steps
lem-nat-2-SBOX⟨1·0·42·3⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-43-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨1·0·42·3⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb1-0-42-3 ∷ []) (Sb1-0-43-2 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (refl) ▸
       at 0 2 (Bx1-0432 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0423⟩ c4) ▸
       at 1 2 (Toff234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ Toff324 ∷ []) (Toff234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb1-0-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·3·2⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ Toff324 ∷ []) (Toff234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sb⁻1-0-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·3·2⟩ c4) ▸
       at 0 5 (Sb1-0-43-2 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;104): 8 steps
lem-nat-1-BOX⟨3·104⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx3-104 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-204 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·104⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-104 ∷ []) (Bx3-204 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff301 ∷ Bx1-34 ∷ Toff301 ∷ CCZ013 ∷ Bx1-34 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 1 2 (Toff302 ∷ Sw12 ∷ []) (lem-nat-1-TOFF301 c4) ▸
       at 2 2 (Bx2-34 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·34⟩ c4) ▸
       at 3 2 (Toff302 ∷ Sw12 ∷ []) (lem-nat-1-TOFF301 c4) ▸
       at 4 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 5 2 (Bx2-34 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·34⟩ c4) ▸
       at 0 6 (Bx3-204 ∷ []) (refl) ▸ done


-- nat 1 BOX(1;3204): 8 steps
lem-nat-1-BOX⟨1·3204⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx1-3204 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3104 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·3204⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-3204 ∷ []) (Bx2-3104 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff123 ∷ Bx3-104 ∷ Toff123 ∷ CCZ123 ∷ Bx3-104 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff213 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff123 ∷ []) (Toff213 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx3-204 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·104⟩ c4) ▸
       at 3 2 (Toff213 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff123 ∷ []) (Toff213 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx3-204 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·104⟩ c4) ▸
       at 0 6 (Bx2-3104 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;204): 8 steps
lem-nat-1-BOX⟨3·204⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx3-204 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-104 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·204⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-204 ∷ []) (Bx3-104 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff302 ∷ Bx2-34 ∷ Toff302 ∷ CCZ023 ∷ Bx2-34 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 1 2 (Toff301 ∷ Sw12 ∷ []) (lem-nat-1-TOFF302 c4) ▸
       at 2 2 (Bx1-34 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·34⟩ c4) ▸
       at 3 2 (Toff301 ∷ Sw12 ∷ []) (lem-nat-1-TOFF302 c4) ▸
       at 4 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 5 2 (Bx1-34 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·34⟩ c4) ▸
       at 0 6 (Bx3-104 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;3104): 8 steps
lem-nat-1-BOX⟨2·3104⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx2-3104 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3204 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·3104⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-3104 ∷ []) (Bx1-3204 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff213 ∷ Bx3-204 ∷ Toff213 ∷ CCZ123 ∷ Bx3-204 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff213 ∷ []) (Toff123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx3-104 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·204⟩ c4) ▸
       at 3 2 (Toff123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff213 ∷ []) (Toff123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx3-104 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·204⟩ c4) ▸
       at 0 6 (Bx1-3204 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;24): 3 steps
lem-nat-2-BOX⟨1·24⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx1-24 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-34 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·24⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-24 ∷ []) (Bx1-34 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ24 ∷ []) (refl) ▸
       at 0 2 (CZ34 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CZ24 ∷ []) (CZ34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx1-34 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;104): 8 steps
lem-nat-2-BOX⟨2·104⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx2-104 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-104 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·104⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-104 ∷ []) (Bx3-104 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff201 ∷ Bx1-24 ∷ Toff201 ∷ CCZ012 ∷ Bx1-24 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 1 2 (Toff301 ∷ Sw23 ∷ []) (lem-nat-2-TOFF201 c4) ▸
       at 2 2 (Bx1-34 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·24⟩ c4) ▸
       at 3 2 (Toff301 ∷ Sw23 ∷ []) (lem-nat-2-TOFF201 c4) ▸
       at 4 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 5 2 (Bx1-34 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·24⟩ c4) ▸
       at 0 6 (Bx3-104 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;2304): 8 steps
lem-nat-2-BOX⟨1·2304⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx1-2304 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3204 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·2304⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-2304 ∷ []) (Bx1-3204 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff123 ∷ Bx2-104 ∷ Toff123 ∷ CCZ123 ∷ Bx2-104 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff123 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff123 ∷ []) (Toff123 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx3-104 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·104⟩ c4) ▸
       at 3 2 (Toff123 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff123 ∷ []) (Toff123 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ123 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx3-104 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·104⟩ c4) ▸
       at 0 6 (Bx1-3204 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;34): 3 steps
lem-nat-2-BOX⟨1·34⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx1-34 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-24 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·34⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-34 ∷ []) (Bx1-24 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ34 ∷ []) (refl) ▸
       at 0 2 (CZ24 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CZ34 ∷ []) (CZ24 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx1-24 ∷ []) (refl) ▸ done


-- nat 2 BOX(3;104): 8 steps
lem-nat-2-BOX⟨3·104⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx3-104 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-104 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·104⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-104 ∷ []) (Bx2-104 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff301 ∷ Bx1-34 ∷ Toff301 ∷ CCZ013 ∷ Bx1-34 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 1 2 (Toff201 ∷ Sw23 ∷ []) (lem-nat-2-TOFF301 c4) ▸
       at 2 2 (Bx1-24 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·34⟩ c4) ▸
       at 3 2 (Toff201 ∷ Sw23 ∷ []) (lem-nat-2-TOFF301 c4) ▸
       at 4 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 5 2 (Bx1-24 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·34⟩ c4) ▸
       at 0 6 (Bx2-104 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;3204): 8 steps
lem-nat-2-BOX⟨1·3204⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx1-3204 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2304 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·3204⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-3204 ∷ []) (Bx1-2304 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff123 ∷ Bx3-104 ∷ Toff123 ∷ CCZ123 ∷ Bx3-104 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff123 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff123 ∷ []) (Toff123 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx2-104 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·104⟩ c4) ▸
       at 3 2 (Toff123 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff123 ∷ []) (Toff123 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ123 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx2-104 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·104⟩ c4) ▸
       at 0 6 (Bx1-2304 ∷ []) (refl) ▸ done


-- nat 3 BOX(1;23): 3 steps
lem-nat-3-BOX⟨1·23⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx1-23 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-24 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨1·23⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx1-23 ∷ []) (Bx1-24 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ23 ∷ []) (refl) ▸
       at 0 2 (CZ24 ∷ Sw34 ∷ []) (lem-nat-3-CZ23 c4) ▸
       at 0 1 (Bx1-24 ∷ []) (refl) ▸ done


-- nat 3 BOX(2;103): 8 steps
lem-nat-3-BOX⟨2·103⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx2-103 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-104 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·103⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx2-103 ∷ []) (Bx2-104 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff201 ∷ Bx1-23 ∷ Toff201 ∷ CCZ012 ∷ Bx1-23 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 1 2 (Toff201 ∷ Sw34 ∷ []) (sym (c₃ (Toffᵗ) (Swap))) ▸
       at 2 2 (Bx1-24 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·23⟩ c4) ▸
       at 3 2 (Toff201 ∷ Sw34 ∷ []) (sym (c₃ (Toffᵗ) (Swap))) ▸
       at 4 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 5 2 (Bx1-24 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·23⟩ c4) ▸
       at 0 6 (Bx2-104 ∷ []) (refl) ▸ done


-- nat 3 BOX(1;2403): 8 steps
lem-nat-3-BOX⟨1·2403⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx1-2403 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2304 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨1·2403⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx1-2403 ∷ []) (Bx1-2304 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff124 ∷ Bx2-103 ∷ Toff124 ∷ CCZ124 ∷ Bx2-103 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw34 ∷ []) (lem-nat-3-CCZ124 c4) ▸
       at 1 2 (Toff123 ∷ Sw34 ∷ []) (lem-nat-3-TOFF124 c4) ▸
       at 2 2 (Bx2-104 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·103⟩ c4) ▸
       at 3 2 (Toff123 ∷ Sw34 ∷ []) (lem-nat-3-TOFF124 c4) ▸
       at 4 2 (CCZ123 ∷ Sw34 ∷ []) (lem-nat-3-CCZ124 c4) ▸
       at 5 2 (Bx2-104 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·103⟩ c4) ▸
       at 0 6 (Bx1-2304 ∷ []) (refl) ▸ done


-- nat 3 BOX(1;24): 3 steps
lem-nat-3-BOX⟨1·24⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx1-24 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-23 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨1·24⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx1-24 ∷ []) (Bx1-23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ24 ∷ []) (refl) ▸
       at 0 2 (CZ23 ∷ Sw34 ∷ []) (lem-nat-3-CZ24 c4) ▸
       at 0 1 (Bx1-23 ∷ []) (refl) ▸ done


-- nat 3 BOX(2;104): 8 steps
lem-nat-3-BOX⟨2·104⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx2-104 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-103 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·104⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx2-104 ∷ []) (Bx2-103 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff201 ∷ Bx1-24 ∷ Toff201 ∷ CCZ012 ∷ Bx1-24 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 1 2 (Toff201 ∷ Sw34 ∷ []) (sym (c₃ (Toffᵗ) (Swap))) ▸
       at 2 2 (Bx1-23 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·24⟩ c4) ▸
       at 3 2 (Toff201 ∷ Sw34 ∷ []) (sym (c₃ (Toffᵗ) (Swap))) ▸
       at 4 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 5 2 (Bx1-23 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·24⟩ c4) ▸
       at 0 6 (Bx2-103 ∷ []) (refl) ▸ done


-- nat 3 BOX(1;2304): 8 steps
lem-nat-3-BOX⟨1·2304⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx1-2304 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2403 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨1·2304⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx1-2304 ∷ []) (Bx1-2403 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff123 ∷ Bx2-104 ∷ Toff123 ∷ CCZ123 ∷ Bx2-104 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw34 ∷ []) (lem-nat-3-CCZ123 c4) ▸
       at 1 2 (Toff124 ∷ Sw34 ∷ []) (lem-nat-3-TOFF123 c4) ▸
       at 2 2 (Bx2-103 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·104⟩ c4) ▸
       at 3 2 (Toff124 ∷ Sw34 ∷ []) (lem-nat-3-TOFF123 c4) ▸
       at 4 2 (CCZ124 ∷ Sw34 ∷ []) (lem-nat-3-CCZ123 c4) ▸
       at 5 2 (Bx2-103 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·104⟩ c4) ▸
       at 0 6 (Bx1-2403 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;13): 3 steps
lem-nat-1-BOX⟨2·13⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx2-13 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-23 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·13⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-13 ∷ []) (Bx1-23 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ13 ∷ []) (refl) ▸
       at 0 2 (CZ23 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CZ13 ∷ []) (CZ23 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx1-23 ∷ []) (refl) ▸ done


-- nat 1 BOX(1;203): 8 steps
lem-nat-1-BOX⟨1·203⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx1-203 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-103 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·203⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-203 ∷ []) (Bx2-103 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff102 ∷ Bx2-13 ∷ Toff102 ∷ CCZ012 ∷ Bx2-13 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff201 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff102 ∷ []) (Toff201 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx1-23 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·13⟩ c4) ▸
       at 3 2 (Toff201 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff102 ∷ []) (Toff201 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx1-23 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·13⟩ c4) ▸
       at 0 6 (Bx2-103 ∷ []) (refl) ▸ done


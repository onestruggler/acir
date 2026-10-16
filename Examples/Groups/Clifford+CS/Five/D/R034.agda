{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R034 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-2-CCZ012 ; lem-nat-2-CCZ013 ; lem-nat-2-CCZ024 ; lem-nat-2-CCZ034 ; lem-nat-2-TOFF024 ; lem-nat-2-TOFF034 ; lem-nat-2-TOFF102 ; lem-nat-2-TOFF103)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-2-CCZ124 ; lem-nat-2-CCZ134 ; lem-nat-2-TOFF304)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-CCZ014 ; lem-nat-0-TOFF014)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-0-CCZ034 ; lem-nat-0-CCZ134 ; lem-nat-0-TOFF403)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-3-TOFF214)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-0-TOFF214)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-0-TOFF024 ; lem-nat-0-TOFF401 ; lem-nat-2-TOFF214 ; lem-nat-2-TOFF402)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-3-CCZ123 ; lem-nat-3-CCZ124)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-nat-2-CZ12 ; lem-nat-2-CZ13)
open import Examples.Groups.Clifford+CS.Five.D.R013 using (lem-nat-2-CS13 ; lem-nat-2-CSd13 ; lem-nat-2-TOFF314)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-0-TOFF134 ; lem-nat-2-TOFF124)
open import Examples.Groups.Clifford+CS.Five.D.R016 using (lem-nat-0-BOX⟨0·3142⟩)
open import Examples.Groups.Clifford+CS.Five.D.R020 using (lem-nat-3-TOFF213)
open import Examples.Groups.Clifford+CS.Five.D.R022 using (lem-nat-0-BOX⟨1·0432⟩)
open import Examples.Groups.Clifford+CS.Five.D.R023 using (lem-nat-3-BOX⟨1·23⟩ ; lem-nat-3-BOX⟨1·24⟩)
open import Examples.Groups.Clifford+CS.Five.D.R024 using (lem-nat-2-BOX⟨1·32⟩)
open import Examples.Groups.Clifford+CS.Five.D.R027 using (lem-nat-2-BOX⟨1·23⟩)
open import Examples.Groups.Clifford+CS.Five.D.R030 using (lem-nat-0-BOX⟨4·02⟩ ; lem-nat-0-BOX⟨4·12⟩)
open import Examples.Groups.Clifford+CS.Five.D.R031 using (lem-nat-0-BOX⟨1·3240⟩ ; lem-nat-1-BOX⟨0·3241⟩)
open import Examples.Groups.Clifford+CS.Five.D.R033 using (lem-nat-0-SBOX⟨1·0·2·3⟩ ; lem-nat-0-SBOXd⟨1·0·2·3⟩)
-- nat 0 SBOX(1;0;43;2): 7 steps
lem-nat-0-SBOX⟨1·0·43·2⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-43-2 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨1·0·43·2⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb1-0-43-2 ∷ []) (Sb0-1-43-2 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 0 2 (Bx0-1432 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0432⟩ c4) ▸
       at 1 2 (Toff234 ∷ Sw01 ∷ []) (c₂ (Swap) (Toff)) ▸
       at 2 2 (Sb0-1-2-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·2·3⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw01 ∷ []) (c₂ (Swap) (Toff)) ▸
       at 4 2 (Sb⁻0-1-2-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·2·3⟩ c4) ▸
       at 0 5 (Sb0-1-43-2 ∷ []) (refl) ▸ done


-- resp TOFF403 at 2: 236 steps
lem-resp-TOFF403-at-2 : Complete 4 → ⟪ (Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ Toff413 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-TOFF403-at-2 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (run b29)))))))))))))))))))))))))))))
  where
  b0 : Chain (Toff403 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sw23 ∷ Toff402 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw12 ∷ Toff401 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Toff301 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (K3 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ K2 ∷ []) (K3 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ Sw23 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ [])
  b1 = at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K3 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ K2 ∷ []) (K3 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ Sw23 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ Sw34 ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ [])
  b2 = at 10 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 11 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 2 2 (K4 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ K3 ∷ []) (K4 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (Sw23 ∷ Sw12 ∷ K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ Sw34 ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ []) (Sw23 ∷ K4 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ [])
  b3 = at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 9 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 7 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K4 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ K3 ∷ []) (K4 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 10 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑)) ▸
       at 2 2 (CS24 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS14 ∷ []) (CS24 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸ done

  b4 : Chain (Sw23 ∷ K4 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ []) (Sw23 ∷ K4 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw12 ∷ Sw34 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ [])
  b4 = at 5 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS24⁻ ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS14⁻ ∷ []) (CS24⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 7 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 7 2 (CS03 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS03 ∷ []) (CS03 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸ done

  b5 : Chain (Sw23 ∷ K4 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw12 ∷ Sw34 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ []) (K4 ∷ CS34 ∷ Sw23 ∷ CX02 ∷ Sw23 ∷ Sw23 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K4 ∷ ι ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ [])
  b5 = at 8 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑)) ▸
       at 8 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 9 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸
       at 0 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸
       at 1 2 (CS34 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS24 ∷ []) (CS34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸ done

  b6 : Chain (K4 ∷ CS34 ∷ Sw23 ∷ CX02 ∷ Sw23 ∷ Sw23 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K4 ∷ ι ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ []) (K4 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ K4 ∷ ι ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ [])
  b6 = at 2 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS34⁻ ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS24⁻ ∷ []) (CS34⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (lw0 c4 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 8 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸ done

  b7 : Chain (K4 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ K4 ∷ ι ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ []) (K4 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Sw12 ∷ K4 ∷ ι ∷ Sw12 ∷ [])
  b7 = at 9 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 10 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (lw0 c4 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸
       at 7 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 8 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 (Sw12 ∷ ι ∷ []) (c₁ (iI) (Swap)) ▸
       at 6 2 (Sw12 ∷ K4 ∷ []) (sym (c₃ (Swap ↑) (K ↑))) ▸ done

  b8 : Chain (K4 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Sw12 ∷ K4 ∷ ι ∷ Sw12 ∷ []) (K4 ∷ CS34 ∷ Sw12 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K4 ∷ ι ∷ Sw12 ∷ [])
  b8 = at 5 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 6 2 (Sw12 ∷ CS03 ∷ []) (lw4 c4 (CS03 ∷ Sw12 ∷ []) (Sw12 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw12 ∷ CX03 ∷ []) (lw4 c4 (CX03 ∷ Sw12 ∷ []) (Sw12 ∷ CX03 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Sw12 ∷ CS34⁻ ∷ []) (sym (c₃ (Swap ↑) (CS • CS • CS))) ▸
       at 2 2 (Sw12 ∷ CX03 ∷ []) (lw4 c4 (CX03 ∷ Sw12 ∷ []) (Sw12 ∷ CX03 ∷ []) tt tt Eq.refl) ▸ done

  b9 : Chain (K4 ∷ CS34 ∷ Sw12 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K4 ∷ ι ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ K4 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ Sw23 ∷ CX03 ∷ CS04 ∷ K4 ∷ ι ∷ Sw12 ∷ [])
  b9 = at 1 2 (Sw12 ∷ CS34 ∷ []) (sym (c₃ (Swap ↑) (CS))) ▸
       at 0 2 (Sw12 ∷ K4 ∷ []) (sym (c₃ (Swap ↑) (K ↑))) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸
       at 3 2 (CS24 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS34 ∷ []) (CS24 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 (CS24⁻ ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS34⁻ ∷ []) (CS24⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸ done

  b10 : Chain (Sw12 ∷ Sw23 ∷ K4 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ Sw23 ∷ CX03 ∷ CS04 ∷ K4 ∷ ι ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ K4 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw23 ∷ K4 ∷ ι ∷ Sw12 ∷ [])
  b10 = at 7 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 8 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (lw0 c4 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 10 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 11 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 12 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (lw0 c4 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸ done

  b11 : Chain (Sw12 ∷ Sw23 ∷ K4 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw23 ∷ K4 ∷ ι ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ K4 ∷ CS14 ∷ CX01 ∷ Sw12 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K4 ∷ ι ∷ Sw23 ∷ Sw12 ∷ [])
  b11 = at 7 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑)) ▸
       at 4 2 (CS14 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS24 ∷ []) (CS14 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done

  b12 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ K4 ∷ CS14 ∷ CX01 ∷ Sw12 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K4 ∷ ι ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw12 ∷ K4 ∷ ι ∷ Sw23 ∷ Sw12 ∷ [])
  b12 = at 6 2 (CS14⁻ ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS24⁻ ∷ []) (CS14⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 8 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸
       at 9 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 9 2 (CS03 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS03 ∷ []) (CS03 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 8 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done

  b13 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw12 ∷ K4 ∷ ι ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ Sw34 ∷ Sw34 ∷ CS13⁻ ∷ Sw34 ∷ CX01 ∷ CS04 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ [])
  b13 = at 9 2 (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑)) ▸
       at 10 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 3 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (K3 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ K4 ∷ []) (K3 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b14 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ Sw34 ∷ Sw34 ∷ CS13⁻ ∷ Sw34 ∷ CX01 ∷ CS04 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K2 ∷ Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ [])
  b14 = at 7 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 10 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 10 2 (K3 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ K4 ∷ []) (K3 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (K2 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ K3 ∷ []) (K2 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸ done

  b15 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K2 ∷ Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ [])
  b15 = at 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done

  b16 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Toff403 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b16 = at 11 2 (K2 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ K3 ∷ []) (K2 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 5 8 (Toff201 ∷ []) (by-assoc Eq.refl) ▸
       at 4 3 (Toff301 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (Toff401 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff402 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff403 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸ done

  b17 : Chain (Sw12 ∷ Toff403 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b17 = at 1 1 (Sw23 ∷ Toff402 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw12 ∷ Toff401 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ Toff301 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (K3 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ K2 ∷ []) (K3 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b18 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b18 = at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 7 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (K3 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ K2 ∷ []) (K3 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸ done

  b19 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b19 = at 12 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 (K4 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ K3 ∷ []) (K4 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸ done

  b20 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ K4 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b20 = at 10 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 8 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K4 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ K3 ∷ []) (K4 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 11 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 2 2 (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑)) ▸
       at 3 2 (CS24 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS14 ∷ []) (CS24 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸ done

  b21 : Chain (Sw12 ∷ Sw23 ∷ K4 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ K4 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b21 = at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS24⁻ ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS14⁻ ∷ []) (CS24⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 8 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 8 2 (CS03 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS03 ∷ []) (CS03 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸ done

  b22 : Chain (Sw12 ∷ Sw23 ∷ K4 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ K4 ∷ CS34 ∷ CX03 ∷ Sw23 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K4 ∷ ι ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b22 = at 7 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑)) ▸
       at 9 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 10 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸
       at 2 2 (CS34 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS24 ∷ []) (CS34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸ done

  b23 : Chain (Sw12 ∷ K4 ∷ CS34 ∷ CX03 ∷ Sw23 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K4 ∷ ι ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ K4 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ K4 ∷ ι ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b23 = at 4 2 (CS34⁻ ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS24⁻ ∷ []) (CS34⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (lw0 c4 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 9 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 10 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸ done

  b24 : Chain (Sw12 ∷ K4 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ K4 ∷ ι ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ K4 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw01 ∷ K4 ∷ ι ∷ Sw01 ∷ Sw12 ∷ [])
  b24 = at 11 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (lw0 c4 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 6 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 9 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 (Sw01 ∷ ι ∷ []) (lw4 c4 (ι ∷ Sw01 ∷ []) (Sw01 ∷ ι ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Sw01 ∷ K4 ∷ []) (sym (c₂ (Swap) (K ↑ ↑))) ▸
       at 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b25 : Chain (Sw12 ∷ K4 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw01 ∷ K4 ∷ ι ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ K4 ∷ Sw01 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K4 ∷ ι ∷ Sw01 ∷ Sw12 ∷ [])
  b25 = at 8 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 7 2 (Sw01 ∷ CS13 ∷ []) (lw4 c4 (CS03 ∷ Sw01 ∷ []) (Sw01 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 7 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw01 ∷ CX13 ∷ []) (lw4 c4 (CX03 ∷ Sw01 ∷ []) (Sw01 ∷ CX13 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sw01 ∷ CS34⁻ ∷ []) (sym (c₂ (Swap) ((CS • CS • CS) ↑))) ▸
       at 3 2 (Sw01 ∷ CX13 ∷ []) (lw4 c4 (CX03 ∷ Sw01 ∷ []) (Sw01 ∷ CX13 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sw01 ∷ CS34 ∷ []) (sym (c₂ (Swap) (CS ↑))) ▸ done

  b26 : Chain (Sw12 ∷ K4 ∷ Sw01 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K4 ∷ ι ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ Sw23 ∷ K4 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Sw23 ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ CS14 ∷ K4 ∷ ι ∷ Sw01 ∷ Sw12 ∷ [])
  b26 = at 1 2 (Sw01 ∷ K4 ∷ []) (sym (c₂ (Swap) (K ↑ ↑))) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸
       at 4 2 (CS24 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS34 ∷ []) (CS24 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 (CS24⁻ ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS34⁻ ∷ []) (CS24⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 8 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b27 : Chain (Sw12 ∷ Sw01 ∷ Sw23 ∷ K4 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Sw23 ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ CS14 ∷ K4 ∷ ι ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw34 ∷ K3 ∷ CS23 ∷ Sw34 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K4 ∷ ι ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ [])
  b27 = at 7 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 (CS14 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS14 ∷ []) (CS14 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸
       at 10 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 3 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (K3 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ K4 ∷ []) (K3 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done

  b28 : Chain (Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw34 ∷ K3 ∷ CS23 ∷ Sw34 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K4 ∷ ι ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw34 ∷ K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ [])
  b28 = at 6 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 8 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 10 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 10 2 (K3 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ K4 ∷ []) (K3 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸ done

  b29 : Chain (Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw34 ∷ K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ Toff413 ∷ Sw01 ∷ Sw12 ∷ [])
  b29 = at 4 8 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) (lw4 c4 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι ∷ []) (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) tt tt Eq.refl) ▸
       at 4 8 (Toff312 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (Toff412 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff413 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 1 CK20: 2 steps
lem-nat-1-CK20 : Complete 4 → ⟪ (Sw12 ∷ CK20 ∷ []) ⟫ʷ ≈ ⟪ (CK10 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-CK20 c4 = run b0
  where
  b0 : Chain (Sw12 ∷ CK20 ∷ []) (CK10 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- nat 1 CK10: 2 steps
lem-nat-1-CK10 : Complete 4 → ⟪ (Sw12 ∷ CK10 ∷ []) ⟫ʷ ≈ ⟪ (CK20 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-CK10 c4 = run b0
  where
  b0 : Chain (Sw12 ∷ CK10 ∷ []) (CK20 ∷ Sw12 ∷ [])
  b0 = at 2 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (CK20 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 CK30: 2 steps
lem-nat-2-CK30 : Complete 4 → ⟪ (Sw23 ∷ CK30 ∷ []) ⟫ʷ ≈ ⟪ (CK20 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-CK30 c4 = run b0
  where
  b0 : Chain (Sw23 ∷ CK30 ∷ []) (CK20 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- nat 2 CK20: 2 steps
lem-nat-2-CK20 : Complete 4 → ⟪ (Sw23 ∷ CK20 ∷ []) ⟫ʷ ≈ ⟪ (CK30 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-CK20 c4 = run b0
  where
  b0 : Chain (Sw23 ∷ CK20 ∷ []) (CK30 ∷ Sw23 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (CK30 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 CK40: 2 steps
lem-nat-3-CK40 : Complete 4 → ⟪ (Sw34 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK30 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-CK40 c4 = run b0
  where
  b0 : Chain (Sw34 ∷ CK40 ∷ []) (CK30 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- nat 3 CK30: 2 steps
lem-nat-3-CK30 : Complete 4 → ⟪ (Sw34 ∷ CK30 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-CK30 c4 = run b0
  where
  b0 : Chain (Sw34 ∷ CK30 ∷ []) (CK40 ∷ Sw34 ∷ [])
  b0 = at 2 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (CK40 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 CK40: 7 steps
lem-nat-2-CK40 : Complete 4 → ⟪ (Sw23 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-CK40 c4 = run b0
  where
  b0 : Chain (Sw23 ∷ CK40 ∷ []) (CK40 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (lw0 c4 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 3 2 (CK10 ∷ Sw34 ∷ []) (sym (c₂ (CK₁₀) (Swap ↑))) ▸
       at 4 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 5 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (lw0 c4 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 7 (CK40 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 1 CK40: 5 steps
lem-nat-1-CK40 : Complete 4 → ⟪ (Sw12 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-CK40 c4 = run b0
  where
  b0 : Chain (Sw12 ∷ CK40 ∷ []) (CK40 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 1 2 (CK30 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CK30 ∷ []) (CK30 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 0 3 (CK40 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 CK41: 5 steps
lem-nat-0-CK41 : Complete 4 → ⟪ (Sw01 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-CK41 c4 = run b0
  where
  b0 : Chain (Sw01 ∷ CK41 ∷ []) (CK40 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CK31 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 1 2 (CK30 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CK31 ∷ []) (CK30 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 0 3 (CK40 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 CK40: 5 steps
lem-nat-0-CK40 : Complete 4 → ⟪ (Sw01 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-CK40 c4 = run b0
  where
  b0 : Chain (Sw01 ∷ CK40 ∷ []) (CK41 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 1 2 (CK31 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CK30 ∷ []) (CK31 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 0 3 (CK41 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 BOX(0;31): 3 steps
lem-nat-2-BOX⟨0·31⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx0-31 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-21 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·31⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-31 ∷ []) (Bx0-21 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ13 ∷ []) (refl) ▸
       at 0 2 (CZ12 ∷ Sw23 ∷ []) (lem-nat-2-CZ13 c4) ▸
       at 0 1 (Bx0-21 ∷ []) (refl) ▸ done


-- nat 2 BOX(3;041): 8 steps
lem-nat-2-BOX⟨3·041⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx3-041 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-041 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·041⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-041 ∷ []) (Bx2-041 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff304 ∷ Bx0-31 ∷ Toff304 ∷ CCZ034 ∷ Bx0-31 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 1 2 (Toff204 ∷ Sw23 ∷ []) (lem-nat-2-TOFF304 c4) ▸
       at 2 2 (Bx0-21 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·31⟩ c4) ▸
       at 3 2 (Toff204 ∷ Sw23 ∷ []) (lem-nat-2-TOFF304 c4) ▸
       at 4 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 5 2 (Bx0-21 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·31⟩ c4) ▸
       at 0 6 (Bx2-041 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;3241): 8 steps
lem-nat-2-BOX⟨0·3241⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx0-3241 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·3241⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-3241 ∷ []) (Bx0-2341 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff023 ∷ Bx3-041 ∷ Toff023 ∷ CCZ023 ∷ Bx3-041 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff023 ∷ []) (Toff023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx2-041 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·041⟩ c4) ▸
       at 3 2 (Toff023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff023 ∷ []) (Toff023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx2-041 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·041⟩ c4) ▸
       at 0 6 (Bx0-2341 ∷ []) (refl) ▸ done


-- nat 2 SBOX(0;3;1;4): 3 steps
lem-nat-2-SBOX⟨0·3·1·4⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb0-3-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-1-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨0·3·1·4⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb0-3-1-4 ∷ []) (Sb0-2-1-4 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS13 ∷ []) (refl) ▸
       at 0 2 (CS12 ∷ Sw23 ∷ []) (lem-nat-2-CS13 c4) ▸
       at 0 1 (Sb0-2-1-4 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(0;3;1;4): 3 steps
lem-nat-2-SBOXd⟨0·3·1·4⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb⁻0-3-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-2-1-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨0·3·1·4⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻0-3-1-4 ∷ []) (Sb⁻0-2-1-4 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS13⁻ ∷ []) (refl) ▸
       at 0 2 (CS12⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd13 c4) ▸
       at 0 1 (Sb⁻0-2-1-4 ∷ []) (refl) ▸ done


-- nat 2 SBOX(0;3;24;1): 7 steps
lem-nat-2-SBOX⟨0·3·24·1⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb0-3-24-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-34-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨0·3·24·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb0-3-24-1 ∷ []) (Sb0-2-34-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx0-3241 ∷ Toff124 ∷ Sb0-3-1-4 ∷ Toff124 ∷ Sb⁻0-3-1-4 ∷ []) (refl) ▸
       at 0 2 (Bx0-2341 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3241⟩ c4) ▸
       at 1 2 (Toff134 ∷ Sw23 ∷ []) (lem-nat-2-TOFF124 c4) ▸
       at 2 2 (Sb0-2-1-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·3·1·4⟩ c4) ▸
       at 3 2 (Toff134 ∷ Sw23 ∷ []) (lem-nat-2-TOFF124 c4) ▸
       at 4 2 (Sb⁻0-2-1-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·3·1·4⟩ c4) ▸
       at 0 5 (Sb0-2-34-1 ∷ []) (refl) ▸ done


-- nat 0 SBOX(1;3;0;4): 3 steps
lem-nat-0-SBOX⟨1·3·0·4⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb1-3-0-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-3-1-4 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨1·3·0·4⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb1-3-0-4 ∷ []) (Sb0-3-1-4 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS03 ∷ []) (refl) ▸
       at 0 2 (CS13 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS03 ∷ []) (CS13 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-3-1-4 ∷ []) (refl) ▸ done


-- nat 0 SBOXd(1;3;0;4): 3 steps
lem-nat-0-SBOXd⟨1·3·0·4⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb⁻1-3-0-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-3-1-4 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨1·3·0·4⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻1-3-0-4 ∷ []) (Sb⁻0-3-1-4 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 2 (CS13⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS03⁻ ∷ []) (CS13⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻0-3-1-4 ∷ []) (refl) ▸ done


-- nat 0 SBOX(1;3;24;0): 7 steps
lem-nat-0-SBOX⟨1·3·24·0⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb1-3-24-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-3-24-1 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨1·3·24·0⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb1-3-24-0 ∷ []) (Sb0-3-24-1 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx1-3240 ∷ Toff024 ∷ Sb1-3-0-4 ∷ Toff024 ∷ Sb⁻1-3-0-4 ∷ []) (refl) ▸
       at 0 2 (Bx0-3241 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·3240⟩ c4) ▸
       at 1 2 (Toff124 ∷ Sw01 ∷ []) (lem-nat-0-TOFF024 c4) ▸
       at 2 2 (Sb0-3-1-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·3·0·4⟩ c4) ▸
       at 3 2 (Toff124 ∷ Sw01 ∷ []) (lem-nat-0-TOFF024 c4) ▸
       at 4 2 (Sb⁻0-3-1-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·3·0·4⟩ c4) ▸
       at 0 5 (Sb0-3-24-1 ∷ []) (refl) ▸ done


-- nat 1 SBOX(0;3;1;4): 3 steps
lem-nat-1-SBOX⟨0·3·1·4⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb0-3-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-3-2-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨0·3·1·4⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb0-3-1-4 ∷ []) (Sb0-3-2-4 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS13 ∷ []) (refl) ▸
       at 0 2 (CS23 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS13 ∷ []) (CS23 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-3-2-4 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(0;3;1;4): 3 steps
lem-nat-1-SBOXd⟨0·3·1·4⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb⁻0-3-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-3-2-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨0·3·1·4⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻0-3-1-4 ∷ []) (Sb⁻0-3-2-4 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS13⁻ ∷ []) (refl) ▸
       at 0 2 (CS23⁻ ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS13⁻ ∷ []) (CS23⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻0-3-2-4 ∷ []) (refl) ▸ done


-- nat 1 SBOX(0;3;24;1): 7 steps
lem-nat-1-SBOX⟨0·3·24·1⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb0-3-24-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-3-14-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨0·3·24·1⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb0-3-24-1 ∷ []) (Sb0-3-14-2 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx0-3241 ∷ Toff124 ∷ Sb0-3-1-4 ∷ Toff124 ∷ Sb⁻0-3-1-4 ∷ []) (refl) ▸
       at 0 2 (Bx0-3142 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·3241⟩ c4) ▸
       at 1 2 (Toff214 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff124 ∷ []) (Toff214 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb0-3-2-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·3·1·4⟩ c4) ▸
       at 3 2 (Toff214 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff124 ∷ []) (Toff214 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sb⁻0-3-2-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨0·3·1·4⟩ c4) ▸
       at 0 5 (Sb0-3-14-2 ∷ []) (refl) ▸ done


-- nat 0 SBOX(0;3;2;4): 2 steps
lem-nat-0-SBOX⟨0·3·2·4⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb0-3-2-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-3-2-4 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨0·3·2·4⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb0-3-2-4 ∷ []) (Sb1-3-2-4 ∷ Sw01 ∷ [])
  b0 = at 0 2 (Sb0-3-2-4 ∷ Sw01 ∷ []) (c₂ (Swap) (CS)) ▸
       at 0 1 (Sb1-3-2-4 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 SBOXd(0;3;2;4): 2 steps
lem-nat-0-SBOXd⟨0·3·2·4⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb⁻0-3-2-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-3-2-4 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨0·3·2·4⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻0-3-2-4 ∷ []) (Sb⁻1-3-2-4 ∷ Sw01 ∷ [])
  b0 = at 0 2 (Sb⁻0-3-2-4 ∷ Sw01 ∷ []) (c₂ (Swap) (CS • CS • CS)) ▸
       at 0 1 (Sb⁻1-3-2-4 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 SBOX(0;3;14;2): 7 steps
lem-nat-0-SBOX⟨0·3·14·2⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb0-3-14-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-3-04-2 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨0·3·14·2⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb0-3-14-2 ∷ []) (Sb1-3-04-2 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx0-3142 ∷ Toff214 ∷ Sb0-3-2-4 ∷ Toff214 ∷ Sb⁻0-3-2-4 ∷ []) (refl) ▸
       at 0 2 (Bx1-3042 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·3142⟩ c4) ▸
       at 1 2 (Toff204 ∷ Sw01 ∷ []) (lem-nat-0-TOFF214 c4) ▸
       at 2 2 (Sb1-3-2-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·3·2·4⟩ c4) ▸
       at 3 2 (Toff204 ∷ Sw01 ∷ []) (lem-nat-0-TOFF214 c4) ▸
       at 4 2 (Sb⁻1-3-2-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·3·2·4⟩ c4) ▸
       at 0 5 (Sb1-3-04-2 ∷ []) (refl) ▸ done


-- nat 3 BOX(2;143): 8 steps
lem-nat-3-BOX⟨2·143⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx2-143 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-134 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·143⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx2-143 ∷ []) (Bx2-134 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff214 ∷ Bx1-23 ∷ Toff214 ∷ CCZ124 ∷ Bx1-23 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw34 ∷ []) (lem-nat-3-CCZ124 c4) ▸
       at 1 2 (Toff213 ∷ Sw34 ∷ []) (lem-nat-3-TOFF214 c4) ▸
       at 2 2 (Bx1-24 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·23⟩ c4) ▸
       at 3 2 (Toff213 ∷ Sw34 ∷ []) (lem-nat-3-TOFF214 c4) ▸
       at 4 2 (CCZ123 ∷ Sw34 ∷ []) (lem-nat-3-CCZ124 c4) ▸
       at 5 2 (Bx1-24 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·23⟩ c4) ▸
       at 0 6 (Bx2-134 ∷ []) (refl) ▸ done


-- nat 3 BOX(1;2043): 8 steps
lem-nat-3-BOX⟨1·2043⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx1-2043 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2034 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨1·2043⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx1-2043 ∷ []) (Bx1-2034 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff102 ∷ Bx2-143 ∷ Toff102 ∷ CCZ012 ∷ Bx2-143 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 1 2 (Toff102 ∷ Sw34 ∷ []) (sym (c₃ (K ↑ • CCZ • K ↑ • iI) (Swap))) ▸
       at 2 2 (Bx2-134 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·143⟩ c4) ▸
       at 3 2 (Toff102 ∷ Sw34 ∷ []) (sym (c₃ (K ↑ • CCZ • K ↑ • iI) (Swap))) ▸
       at 4 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 5 2 (Bx2-134 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·143⟩ c4) ▸
       at 0 6 (Bx1-2034 ∷ []) (refl) ▸ done


-- nat 3 BOX(2;134): 8 steps
lem-nat-3-BOX⟨2·134⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx2-134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-143 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·134⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx2-134 ∷ []) (Bx2-143 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff213 ∷ Bx1-24 ∷ Toff213 ∷ CCZ123 ∷ Bx1-24 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw34 ∷ []) (lem-nat-3-CCZ123 c4) ▸
       at 1 2 (Toff214 ∷ Sw34 ∷ []) (lem-nat-3-TOFF213 c4) ▸
       at 2 2 (Bx1-23 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·24⟩ c4) ▸
       at 3 2 (Toff214 ∷ Sw34 ∷ []) (lem-nat-3-TOFF213 c4) ▸
       at 4 2 (CCZ124 ∷ Sw34 ∷ []) (lem-nat-3-CCZ123 c4) ▸
       at 5 2 (Bx1-23 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·24⟩ c4) ▸
       at 0 6 (Bx2-143 ∷ []) (refl) ▸ done


-- nat 3 BOX(1;2034): 8 steps
lem-nat-3-BOX⟨1·2034⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx1-2034 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2043 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨1·2034⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx1-2034 ∷ []) (Bx1-2043 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff102 ∷ Bx2-134 ∷ Toff102 ∷ CCZ012 ∷ Bx2-134 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 1 2 (Toff102 ∷ Sw34 ∷ []) (sym (c₃ (K ↑ • CCZ • K ↑ • iI) (Swap))) ▸
       at 2 2 (Bx2-143 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·134⟩ c4) ▸
       at 3 2 (Toff102 ∷ Sw34 ∷ []) (sym (c₃ (K ↑ • CCZ • K ↑ • iI) (Swap))) ▸
       at 4 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 5 2 (Bx2-143 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·134⟩ c4) ▸
       at 0 6 (Bx1-2043 ∷ []) (refl) ▸ done


-- nat 2 BOX(3;142): 8 steps
lem-nat-2-BOX⟨3·142⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx3-142 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-143 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·142⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-142 ∷ []) (Bx2-143 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff314 ∷ Bx1-32 ∷ Toff314 ∷ CCZ134 ∷ Bx1-32 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 1 2 (Toff214 ∷ Sw23 ∷ []) (lem-nat-2-TOFF314 c4) ▸
       at 2 2 (Bx1-23 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·32⟩ c4) ▸
       at 3 2 (Toff214 ∷ Sw23 ∷ []) (lem-nat-2-TOFF314 c4) ▸
       at 4 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 5 2 (Bx1-23 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·32⟩ c4) ▸
       at 0 6 (Bx2-143 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;3042): 8 steps
lem-nat-2-BOX⟨1·3042⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx1-3042 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2043 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·3042⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-3042 ∷ []) (Bx1-2043 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff103 ∷ Bx3-142 ∷ Toff103 ∷ CCZ013 ∷ Bx3-142 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 1 2 (Toff102 ∷ Sw23 ∷ []) (lem-nat-2-TOFF103 c4) ▸
       at 2 2 (Bx2-143 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·142⟩ c4) ▸
       at 3 2 (Toff102 ∷ Sw23 ∷ []) (lem-nat-2-TOFF103 c4) ▸
       at 4 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 5 2 (Bx2-143 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·142⟩ c4) ▸
       at 0 6 (Bx1-2043 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;143): 8 steps
lem-nat-2-BOX⟨2·143⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx2-143 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-142 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·143⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-143 ∷ []) (Bx3-142 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff214 ∷ Bx1-23 ∷ Toff214 ∷ CCZ124 ∷ Bx1-23 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 1 2 (Toff314 ∷ Sw23 ∷ []) (lem-nat-2-TOFF214 c4) ▸
       at 2 2 (Bx1-32 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·23⟩ c4) ▸
       at 3 2 (Toff314 ∷ Sw23 ∷ []) (lem-nat-2-TOFF214 c4) ▸
       at 4 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 5 2 (Bx1-32 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·23⟩ c4) ▸
       at 0 6 (Bx3-142 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;2043): 8 steps
lem-nat-2-BOX⟨1·2043⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx1-2043 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3042 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·2043⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-2043 ∷ []) (Bx1-3042 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff102 ∷ Bx2-143 ∷ Toff102 ∷ CCZ012 ∷ Bx2-143 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 1 2 (Toff103 ∷ Sw23 ∷ []) (lem-nat-2-TOFF102 c4) ▸
       at 2 2 (Bx3-142 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·143⟩ c4) ▸
       at 3 2 (Toff103 ∷ Sw23 ∷ []) (lem-nat-2-TOFF102 c4) ▸
       at 4 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 5 2 (Bx3-142 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·143⟩ c4) ▸
       at 0 6 (Bx1-3042 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;431): 8 steps
lem-nat-2-BOX⟨0·431⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx0-431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-421 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·431⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-431 ∷ []) (Bx0-421 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff034 ∷ Bx4-01 ∷ Toff034 ∷ CCZ034 ∷ Bx4-01 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 1 2 (Toff024 ∷ Sw23 ∷ []) (lem-nat-2-TOFF034 c4) ▸
       at 2 2 (Bx4-01 ∷ Sw23 ∷ []) (sym (c₂ (CZ) (Swap))) ▸
       at 3 2 (Toff024 ∷ Sw23 ∷ []) (lem-nat-2-TOFF034 c4) ▸
       at 4 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 5 2 (Bx4-01 ∷ Sw23 ∷ []) (sym (c₂ (CZ) (Swap))) ▸
       at 0 6 (Bx0-421 ∷ []) (refl) ▸ done


-- nat 2 BOX(4;0231): 8 steps
lem-nat-2-BOX⟨4·0231⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx4-0231 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0321 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·0231⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-0231 ∷ []) (Bx4-0321 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff402 ∷ Bx0-431 ∷ Toff402 ∷ CCZ024 ∷ Bx0-431 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 1 2 (Toff403 ∷ Sw23 ∷ []) (lem-nat-2-TOFF402 c4) ▸
       at 2 2 (Bx0-421 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·431⟩ c4) ▸
       at 3 2 (Toff403 ∷ Sw23 ∷ []) (lem-nat-2-TOFF402 c4) ▸
       at 4 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 5 2 (Bx0-421 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·431⟩ c4) ▸
       at 0 6 (Bx4-0321 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;412): 8 steps
lem-nat-0-BOX⟨0·412⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx0-412 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-402 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·412⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-412 ∷ []) (Bx1-402 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff014 ∷ Bx4-02 ∷ Toff014 ∷ CCZ014 ∷ Bx4-02 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 1 2 (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 c4) ▸
       at 2 2 (Bx4-12 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·02⟩ c4) ▸
       at 3 2 (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 c4) ▸
       at 4 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 5 2 (Bx4-12 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·02⟩ c4) ▸
       at 0 6 (Bx1-402 ∷ []) (refl) ▸ done


-- nat 0 BOX(4;0312): 8 steps
lem-nat-0-BOX⟨4·0312⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx4-0312 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1302 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·0312⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-0312 ∷ []) (Bx4-1302 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff403 ∷ Bx0-412 ∷ Toff403 ∷ CCZ034 ∷ Bx0-412 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 1 2 (Toff413 ∷ Sw01 ∷ []) (lem-nat-0-TOFF403 c4) ▸
       at 2 2 (Bx1-402 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·412⟩ c4) ▸
       at 3 2 (Toff413 ∷ Sw01 ∷ []) (lem-nat-0-TOFF403 c4) ▸
       at 4 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 5 2 (Bx1-402 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·412⟩ c4) ▸
       at 0 6 (Bx4-1302 ∷ []) (refl) ▸ done


-- nat 2 CX13: 2 steps
lem-nat-2-CX13 : Complete 4 → ⟪ (Sw23 ∷ CX13 ∷ []) ⟫ʷ ≈ ⟪ (CX12 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-CX13 c4 = run b0
  where
  b0 : Chain (Sw23 ∷ CX13 ∷ []) (CX12 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- nat 0 BOX(1;432): 8 steps
lem-nat-0-BOX⟨1·432⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx1-432 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-432 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·432⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-432 ∷ []) (Bx0-432 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff134 ∷ Bx4-12 ∷ Toff134 ∷ CCZ134 ∷ Bx4-12 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 1 2 (Toff034 ∷ Sw01 ∷ []) (lem-nat-0-TOFF134 c4) ▸
       at 2 2 (Bx4-02 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·12⟩ c4) ▸
       at 3 2 (Toff034 ∷ Sw01 ∷ []) (lem-nat-0-TOFF134 c4) ▸
       at 4 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 5 2 (Bx4-02 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·12⟩ c4) ▸
       at 0 6 (Bx0-432 ∷ []) (refl) ▸ done


-- nat 0 BOX(4;1032): 8 steps
lem-nat-0-BOX⟨4·1032⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx4-1032 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0132 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·1032⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-1032 ∷ []) (Bx4-0132 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff401 ∷ Bx1-432 ∷ Toff401 ∷ CCZ014 ∷ Bx1-432 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 1 2 (Toff401 ∷ Sw01 ∷ []) (lem-nat-0-TOFF401 c4) ▸
       at 2 2 (Bx0-432 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·432⟩ c4) ▸
       at 3 2 (Toff401 ∷ Sw01 ∷ []) (lem-nat-0-TOFF401 c4) ▸
       at 4 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 5 2 (Bx0-432 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·432⟩ c4) ▸
       at 0 6 (Bx4-0132 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;21): 3 steps
lem-nat-2-BOX⟨0·21⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx0-21 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-31 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·21⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-21 ∷ []) (Bx0-31 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ12 ∷ []) (refl) ▸
       at 0 2 (CZ13 ∷ Sw23 ∷ []) (lem-nat-2-CZ12 c4) ▸
       at 0 1 (Bx0-31 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;031): 8 steps
lem-nat-2-BOX⟨2·031⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx2-031 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-021 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·031⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-031 ∷ []) (Bx3-021 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff302 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff203 ∷ []) (Toff302 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-31 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·21⟩ c4) ▸
       at 3 2 (Toff302 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff203 ∷ []) (Toff302 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx0-31 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·21⟩ c4) ▸
       at 0 6 (Bx3-021 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;2431): 8 steps
lem-nat-2-BOX⟨0·2431⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3421 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·2431⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-2431 ∷ []) (Bx0-3421 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx2-031 ∷ Toff024 ∷ CCZ024 ∷ Bx2-031 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 1 2 (Toff034 ∷ Sw23 ∷ []) (lem-nat-2-TOFF024 c4) ▸
       at 2 2 (Bx3-021 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·031⟩ c4) ▸
       at 3 2 (Toff034 ∷ Sw23 ∷ []) (lem-nat-2-TOFF024 c4) ▸
       at 4 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 5 2 (Bx3-021 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·031⟩ c4) ▸
       at 0 6 (Bx0-3421 ∷ []) (refl) ▸ done


-- nat 3 SBOXd(2;3;4;0): 3 steps
lem-nat-3-SBOXd⟨2·3·4·0⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb⁻2-3-4-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-4-3-0 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨2·3·4·0⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻2-3-4-0 ∷ []) (Sb⁻2-4-3-0 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS34⁻ ∷ []) (refl) ▸
       at 0 2 (CS34⁻ ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻2-4-3-0 ∷ []) (refl) ▸ done


-- nat 3 SBOXd(2;4;3;0): 3 steps
lem-nat-3-SBOXd⟨2·4·3·0⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb⁻2-4-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-3-4-0 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨2·4·3·0⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻2-4-3-0 ∷ []) (Sb⁻2-3-4-0 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS34⁻ ∷ []) (refl) ▸
       at 0 2 (CS34⁻ ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻2-3-4-0 ∷ []) (refl) ▸ done


-- nat 0 SBOXd(2;3;4;1): 2 steps
lem-nat-0-SBOXd⟨2·3·4·1⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb⁻2-3-4-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-3-4-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨2·3·4·1⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻2-3-4-1 ∷ []) (Sb⁻2-3-4-0 ∷ Sw01 ∷ [])
  b0 = at 0 2 (Sb⁻2-3-4-1 ∷ Sw01 ∷ []) (c₂ (Swap) ((CS • CS • CS) ↑)) ▸
       at 0 1 (Sb⁻2-3-4-0 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 SBOXd(2;3;4;0): 2 steps
lem-nat-0-SBOXd⟨2·3·4·0⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb⁻2-3-4-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-3-4-1 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨2·3·4·0⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻2-3-4-0 ∷ []) (Sb⁻2-3-4-1 ∷ Sw01 ∷ [])
  b0 = at 0 2 (Sb⁻2-3-4-0 ∷ Sw01 ∷ []) (c₂ (Swap) ((CS • CS • CS) ↑)) ▸
       at 0 1 (Sb⁻2-3-4-1 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 1 SBOXd(1;3;4;2): 2 steps
lem-nat-1-SBOXd⟨1·3·4·2⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb⁻1-3-4-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-3-4-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨1·3·4·2⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻1-3-4-2 ∷ []) (Sb⁻2-3-4-1 ∷ Sw12 ∷ [])
  b0 = at 0 2 (Sb⁻1-3-4-2 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS • CS • CS)) ▸
       at 0 1 (Sb⁻2-3-4-1 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 1 SBOXd(2;3;4;1): 2 steps
lem-nat-1-SBOXd⟨2·3·4·1⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb⁻2-3-4-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-3-4-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨2·3·4·1⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻2-3-4-1 ∷ []) (Sb⁻1-3-4-2 ∷ Sw12 ∷ [])
  b0 = at 0 2 (Sb⁻2-3-4-1 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS • CS • CS)) ▸
       at 0 1 (Sb⁻1-3-4-2 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 SBOXd(1;2;4;3): 3 steps
lem-nat-2-SBOXd⟨1·2·4·3⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb⁻1-2-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-3-4-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨1·2·4·3⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻1-2-4-3 ∷ []) (Sb⁻1-3-4-2 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS24⁻ ∷ []) (refl) ▸
       at 0 2 (CS34⁻ ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS24⁻ ∷ []) (CS34⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻1-3-4-2 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(1;3;4;2): 3 steps
lem-nat-2-SBOXd⟨1·3·4·2⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb⁻1-3-4-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-2-4-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨1·3·4·2⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻1-3-4-2 ∷ []) (Sb⁻1-2-4-3 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS34⁻ ∷ []) (refl) ▸
       at 0 2 (CS24⁻ ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS34⁻ ∷ []) (CS24⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻1-2-4-3 ∷ []) (refl) ▸ done


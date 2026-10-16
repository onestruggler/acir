{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R008 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL ; wl0001 ; wl0002 ; wl0003 ; wl0006 ; wl0007 ; wl0008 ; wl0009 ; wl0010 ; wl0011 ; wl0012 ; wl0013 ; wl0014 ; wl0015 ; wl0016 ; wl0017 ; wl0018 ; wl0021 ; wl0022 ; wl0023 ; wl0024 ; wl0026 ; wl0029 ; wl0030 ; wl0032 ; wl0034 ; wl0037 ; wl0038 ; wl0043 ; wl0053 ; wl0057 ; wl0058 ; wl0061 ; wl0063 ; wl0064 ; wl0067 ; wl0068 ; wl0076 ; wl0081 ; wl0084 ; wl0087 ; wl0091 ; wl0096 ; wl0099 ; wl0100 ; wl0101 ; wl0102 ; wl0112 ; wl0114 ; wl0130 ; wl0132 ; wl0133 ; wl0137 ; wl0138 ; wl0139 ; wl0140 ; wl0141)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-nat-1-CCZ023 ; lem-nat-1-CCZ024 ; lem-nat-1-CCZ034 ; lem-nat-1-TOFF014 ; lem-nat-1-TOFF024 ; lem-nat-1-TOFF203 ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ013 ; lem-nat-2-CCZ024 ; lem-nat-2-CCZ034 ; lem-nat-2-TOFF013 ; lem-nat-2-TOFF024 ; lem-nat-2-TOFF102 ; lem-nat-3-CCZ014 ; lem-nat-3-CCZ024 ; lem-nat-3-CCZ034 ; lem-nat-3-TOFF013)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-0-CCZ024 ; lem-nat-0-CCZ124 ; lem-nat-1-CCZ013 ; lem-nat-1-CCZ014 ; lem-nat-1-TOFF103 ; lem-nat-3-CCZ013 ; lem-nat-3-CCZ023)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-0-CCZ014 ; lem-nat-0-CCZ034 ; lem-nat-0-CCZ134 ; lem-nat-0-TOFF014 ; lem-nat-0-TOFF304 ; lem-nat-0-TOFF314 ; lem-nat-3-TOFF304)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-TOFF214 ; lem-nat-0-TOFF402 ; lem-nat-3-TOFF023 ; lem-nat-3-TOFF214 ; lem-nat-3-TOFF301)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-BOX⟨0·1234⟩ ; lem-nat-0-BOX⟨1·04⟩ ; lem-nat-1-BOX⟨2·04⟩ ; lem-nat-2-CZ04 ; lem-nat-3-BOX⟨2·0314⟩ ; lem-nat-3-CZ03 ; lem-nat-3-CZ04)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-1-BOX⟨1·0324⟩ ; lem-nat-1-CS01 ; lem-nat-1-CS02 ; lem-nat-1-CZ01 ; lem-nat-1-CZ02)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-0-CS14 ; lem-nat-1-BOX⟨2·1340⟩ ; lem-nat-1-CS04 ; lem-nat-1-CSd02 ; lem-nat-2-TOFF403)
-- nat 1 TOFF034: 134 steps
lem-nat-1-TOFF034 : WsL → ⟪ (Sw12 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-TOFF034 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (run b16))))))))))))))))
  where
  b0 : Chain (Sw12 ∷ Toff034 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Toff024 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw12 ∷ Toff014 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b1 = at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 7 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 11 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸ done

  b2 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b2 = at 12 2 [] (wl0006 c4) ▸
       at 3 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 4 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 6 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸ done

  b3 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Sw12 ∷ Sw23 ∷ K0 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ [])
  b3 = at 10 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 8 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 10 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 11 2 [] (wl0007 c4) ▸
       at 2 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 3 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 c4)) ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸ done

  b4 : Chain (Sw12 ∷ Sw23 ∷ K0 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ []) (Sw12 ∷ Sw23 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ [])
  b4 = at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS24⁻ ∷ Sw12 ∷ []) (sym (wl0009 c4)) ▸
       at 8 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 6 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 8 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸
       at 9 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸ done

  b5 : Chain (Sw12 ∷ Sw23 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ []) (Sw12 ∷ K0 ∷ CS34 ∷ CX03 ∷ Sw23 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0 ∷ ι ∷ Sw23 ∷ [])
  b5 = at 7 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 9 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 10 2 [] (wl0001 c4) ▸
       at 1 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 2 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0011 c4)) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 3 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸ done

  b6 : Chain (Sw12 ∷ K0 ∷ CS34 ∷ CX03 ∷ Sw23 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0 ∷ ι ∷ Sw23 ∷ []) (Sw12 ∷ K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw23 ∷ [])
  b6 = at 4 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0012 c4)) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 5 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0013 c4) ▸
       at 8 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 9 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 10 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸ done

  b7 : Chain (Sw12 ∷ K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw23 ∷ []) (K0 ∷ CS34 ∷ CX03 ∷ Sw12 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K0 ∷ ι ∷ [])
  b7 = at 11 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (sym (wl0013 c4)) ▸
       at 6 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 9 2 [] (wl0006 c4) ▸
       at 0 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 1 2 (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸
       at 2 2 (CX03 ∷ Sw12 ∷ []) (sym (wl0014 c4)) ▸ done

  b8 : Chain (K0 ∷ CS34 ∷ CX03 ∷ Sw12 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K0 ∷ ι ∷ []) (K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K0 ∷ Sw12 ∷ ι ∷ [])
  b8 = at 3 2 (CS34⁻ ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS • CS • CS)) ▸
       at 4 2 (CX03 ∷ Sw12 ∷ []) (sym (wl0014 c4)) ▸
       at 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 6 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸
       at 7 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 5 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸ done

  b9 : Chain (K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K0 ∷ Sw12 ∷ ι ∷ []) (Sw23 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ Sw23 ∷ Sw23 ∷ CX02 ∷ Sw23 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ [])
  b9 = at 7 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 1 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 2 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0015 c4)) ▸
       at 4 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0006 c4) ▸
       at 4 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0016 c4)) ▸
       at 6 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b10 : Chain (Sw23 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ Sw23 ∷ Sw23 ∷ CX02 ∷ Sw23 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ []) (Sw23 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw12 ∷ [])
  b10 = at 5 2 [] (wl0006 c4) ▸
       at 7 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0013 c4) ▸
       at 8 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 9 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 10 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 11 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (sym (wl0013 c4)) ▸
       at 6 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done

  b11 : Chain (Sw23 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ Sw12 ∷ CX02 ∷ CS04 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw12 ∷ [])
  b11 = at 7 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 2 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 3 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0017 c4)) ▸
       at 5 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0001 c4) ▸
       at 5 2 (CS14⁻ ∷ Sw12 ∷ []) (sym (wl0018 c4)) ▸ done

  b12 : Chain (Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ Sw12 ∷ CX02 ∷ CS04 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ Sw12 ∷ ι ∷ Sw23 ∷ Sw12 ∷ [])
  b12 = at 7 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0001 c4) ▸
       at 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 8 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸
       at 9 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 7 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸ done

  b13 : Chain (Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ Sw12 ∷ ι ∷ Sw23 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw34 ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ [])
  b13 = at 9 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 3 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 5 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0007 c4) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0007 c4) ▸ done

  b14 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw34 ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ [])
  b14 = at 7 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 9 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0007 c4) ▸
       at 9 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 10 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 4 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b15 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ Sw23 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ [])
  b15 = at 5 2 [] (wl0006 c4) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0006 c4) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (wl0006 c4) ▸
       at 10 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸ done

  b16 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ Sw23 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Toff034 ∷ Sw12 ∷ [])
  b16 = at 11 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 4 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff014 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff024 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff034 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 1 SBOX(2;1;0;4): 3 steps
lem-nat-1-SBOX⟨2·1·0·4⟩ : WsL → ⟪ (Sw12 ∷ Sb2-1-0-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-0-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨2·1·0·4⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb2-1-0-4 ∷ []) (Sb1-2-0-4 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS01 ∷ []) (refl) ▸
       at 0 2 (CS02 ∷ Sw12 ∷ []) (lem-nat-1-CS01 c4) ▸
       at 0 1 (Sb1-2-0-4 ∷ []) (refl) ▸ done


-- nat 1 CSd01: 2 steps
lem-nat-1-CSd01 : WsL → ⟪ (Sw12 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-CSd01 c4 = run b0
  where
  b0 : Chain (Sw12 ∷ CS01⁻ ∷ []) (CS02⁻ ∷ Sw12 ∷ [])
  b0 = at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 0 3 (CS02⁻ ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 1 SBOXd(2;1;0;4): 3 steps
lem-nat-1-SBOXd⟨2·1·0·4⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻2-1-0-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-2-0-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨2·1·0·4⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻2-1-0-4 ∷ []) (Sb⁻1-2-0-4 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS01⁻ ∷ []) (refl) ▸
       at 0 2 (CS02⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd01 c4) ▸
       at 0 1 (Sb⁻1-2-0-4 ∷ []) (refl) ▸ done


-- nat 1 SBOX(2;1;34;0): 7 steps
lem-nat-1-SBOX⟨2·1·34·0⟩ : WsL → ⟪ (Sw12 ∷ Sb2-1-34-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-34-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨2·1·34·0⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb2-1-34-0 ∷ []) (Sb1-2-34-0 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx2-1340 ∷ Toff034 ∷ Sb2-1-0-4 ∷ Toff034 ∷ Sb⁻2-1-0-4 ∷ []) (refl) ▸
       at 0 2 (Bx1-2340 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·1340⟩ c4) ▸
       at 1 2 (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 c4) ▸
       at 2 2 (Sb1-2-0-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·1·0·4⟩ c4) ▸
       at 3 2 (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 c4) ▸
       at 4 2 (Sb⁻1-2-0-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·1·0·4⟩ c4) ▸
       at 0 5 (Sb1-2-34-0 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;20): 3 steps
lem-nat-0-BOX⟨1·20⟩ : WsL → ⟪ (Sw01 ∷ Bx1-20 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-21 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·20⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-20 ∷ []) (Bx0-21 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ02 ∷ []) (refl) ▸
       at 0 2 (CZ12 ∷ Sw01 ∷ []) (sym (wl0137 c4)) ▸
       at 0 1 (Bx0-21 ∷ []) (refl) ▸ done


-- nat 0 BOX(2;140): 8 steps
lem-nat-0-BOX⟨2·140⟩ : WsL → ⟪ (Sw01 ∷ Bx2-140 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-041 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·140⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-140 ∷ []) (Bx2-041 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff214 ∷ Bx1-20 ∷ Toff214 ∷ CCZ124 ∷ Bx1-20 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 1 2 (Toff204 ∷ Sw01 ∷ []) (lem-nat-0-TOFF214 c4) ▸
       at 2 2 (Bx0-21 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·20⟩ c4) ▸
       at 3 2 (Toff204 ∷ Sw01 ∷ []) (lem-nat-0-TOFF214 c4) ▸
       at 4 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 5 2 (Bx0-21 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·20⟩ c4) ▸
       at 0 6 (Bx2-041 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;2340): 8 steps
lem-nat-0-BOX⟨1·2340⟩ : WsL → ⟪ (Sw01 ∷ Bx1-2340 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·2340⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-2340 ∷ []) (Bx0-2341 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff123 ∷ Bx2-140 ∷ Toff123 ∷ CCZ123 ∷ Bx2-140 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0003 c4)) ▸
       at 1 2 (Toff023 ∷ Sw01 ∷ []) (wl0053 c4) ▸
       at 2 2 (Bx2-041 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·140⟩ c4) ▸
       at 3 2 (Toff023 ∷ Sw01 ∷ []) (wl0053 c4) ▸
       at 4 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0003 c4)) ▸
       at 5 2 (Bx2-041 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·140⟩ c4) ▸
       at 0 6 (Bx0-2341 ∷ []) (refl) ▸ done


-- nat 0 TOFF034: 100 steps
lem-nat-0-TOFF034 : WsL → ⟪ (Sw01 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-TOFF034 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (run b12))))))))))))
  where
  b0 : Chain (Sw01 ∷ Toff034 ∷ []) (Sw01 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Toff024 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw12 ∷ Toff014 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw01 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Sw01 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b1 = at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 7 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 11 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸ done

  b2 : Chain (Sw01 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Sw01 ∷ Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b2 = at 12 2 [] (wl0006 c4) ▸
       at 3 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 4 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 6 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸ done

  b3 : Chain (Sw01 ∷ Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Sw01 ∷ Sw23 ∷ K0 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ [])
  b3 = at 10 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 8 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 10 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 11 2 [] (wl0007 c4) ▸
       at 2 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 3 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 c4)) ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸ done

  b4 : Chain (Sw01 ∷ Sw23 ∷ K0 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ []) (Sw01 ∷ Sw23 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ [])
  b4 = at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS24⁻ ∷ Sw12 ∷ []) (sym (wl0009 c4)) ▸
       at 8 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 6 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 8 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸
       at 9 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸ done

  b5 : Chain (Sw01 ∷ Sw23 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ []) (Sw01 ∷ K0 ∷ CS34 ∷ CX03 ∷ Sw23 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0 ∷ ι ∷ Sw23 ∷ [])
  b5 = at 7 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 9 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 10 2 [] (wl0001 c4) ▸
       at 1 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 2 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0011 c4)) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 3 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸ done

  b6 : Chain (Sw01 ∷ K0 ∷ CS34 ∷ CX03 ∷ Sw23 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0 ∷ ι ∷ Sw23 ∷ []) (Sw01 ∷ K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw23 ∷ [])
  b6 = at 4 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0012 c4)) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 5 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0013 c4) ▸
       at 8 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 9 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 10 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸ done

  b7 : Chain (Sw01 ∷ K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw23 ∷ []) (K1 ∷ CS34 ∷ CX13 ∷ Sw01 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K0 ∷ ι ∷ [])
  b7 = at 11 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (sym (wl0013 c4)) ▸
       at 6 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 9 2 [] (wl0006 c4) ▸
       at 0 2 (K1 ∷ Sw01 ∷ []) (sym (wl0076 c4)) ▸
       at 1 2 (CS34 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑)) ▸
       at 2 2 (CX13 ∷ Sw01 ∷ []) (sym (wl0081 c4)) ▸ done

  b8 : Chain (K1 ∷ CS34 ∷ CX13 ∷ Sw01 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K0 ∷ ι ∷ []) (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1 ∷ Sw01 ∷ ι ∷ [])
  b8 = at 3 2 (CS34⁻ ∷ Sw01 ∷ []) (c₂ (Swap) ((CS • CS • CS) ↑)) ▸
       at 4 2 (CX13 ∷ Sw01 ∷ []) (sym (wl0081 c4)) ▸
       at 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 6 2 (CS13 ∷ Sw01 ∷ []) (sym (wl0061 c4)) ▸
       at 7 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 5 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K1 ∷ Sw01 ∷ []) (sym (wl0076 c4)) ▸ done

  b9 : Chain (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1 ∷ Sw01 ∷ ι ∷ []) (Sw23 ∷ K1 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Sw23 ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ CS14 ∷ K1 ∷ ι ∷ Sw01 ∷ [])
  b9 = at 7 2 (ι ∷ Sw01 ∷ []) (wl0030 c4) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 1 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 2 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0015 c4)) ▸
       at 4 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0006 c4) ▸
       at 4 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0016 c4)) ▸
       at 6 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b10 : Chain (Sw23 ∷ K1 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Sw23 ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ CS14 ∷ K1 ∷ ι ∷ Sw01 ∷ []) (Sw23 ∷ Sw34 ∷ K1 ∷ CS23 ∷ Sw34 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw01 ∷ [])
  b10 = at 5 2 [] (wl0006 c4) ▸
       at 6 2 (CS14 ∷ Sw23 ∷ []) (sym (wl0021 c4)) ▸
       at 7 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 2 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 4 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0007 c4) ▸ done

  b11 : Chain (Sw23 ∷ Sw34 ∷ K1 ∷ CS23 ∷ Sw34 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw01 ∷ []) (Sw23 ∷ Sw34 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw23 ∷ Sw01 ∷ [])
  b11 = at 4 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 6 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0007 c4) ▸
       at 6 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 8 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0007 c4) ▸
       at 8 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 9 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸ done

  b12 : Chain (Sw23 ∷ Sw34 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw23 ∷ Sw01 ∷ []) (Toff134 ∷ Sw01 ∷ [])
  b12 = at 2 8 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (wl0032 c4) ▸
       at 2 8 (Toff123 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff124 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff134 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 SBOX(1;2;0;4): 3 steps
lem-nat-0-SBOX⟨1·2·0·4⟩ : WsL → ⟪ (Sw01 ∷ Sb1-2-0-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-1-4 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨1·2·0·4⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb1-2-0-4 ∷ []) (Sb0-2-1-4 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS02 ∷ []) (refl) ▸
       at 0 2 (CS12 ∷ Sw01 ∷ []) (sym (wl0138 c4)) ▸
       at 0 1 (Sb0-2-1-4 ∷ []) (refl) ▸ done


-- nat 0 SBOXd(1;2;0;4): 3 steps
lem-nat-0-SBOXd⟨1·2·0·4⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻1-2-0-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-2-1-4 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨1·2·0·4⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻1-2-0-4 ∷ []) (Sb⁻0-2-1-4 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS02⁻ ∷ []) (refl) ▸
       at 0 2 (CS12⁻ ∷ Sw01 ∷ []) (sym (wl0139 c4)) ▸
       at 0 1 (Sb⁻0-2-1-4 ∷ []) (refl) ▸ done


-- nat 0 SBOX(1;2;34;0): 7 steps
lem-nat-0-SBOX⟨1·2·34·0⟩ : WsL → ⟪ (Sw01 ∷ Sb1-2-34-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-34-1 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨1·2·34·0⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb1-2-34-0 ∷ []) (Sb0-2-34-1 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx1-2340 ∷ Toff034 ∷ Sb1-2-0-4 ∷ Toff034 ∷ Sb⁻1-2-0-4 ∷ []) (refl) ▸
       at 0 2 (Bx0-2341 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2340⟩ c4) ▸
       at 1 2 (Toff134 ∷ Sw01 ∷ []) (lem-nat-0-TOFF034 c4) ▸
       at 2 2 (Sb0-2-1-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·2·0·4⟩ c4) ▸
       at 3 2 (Toff134 ∷ Sw01 ∷ []) (lem-nat-0-TOFF034 c4) ▸
       at 4 2 (Sb⁻0-2-1-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·2·0·4⟩ c4) ▸
       at 0 5 (Sb0-2-34-1 ∷ []) (refl) ▸ done


-- resp TOFF134 at 2: 4 steps
lem-resp-TOFF134-at-2 : WsL → ⟪ (Toff134 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ Toff234 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-TOFF134-at-2 c4 = run b0
  where
  b0 : Chain (Toff134 ∷ []) (Sw12 ∷ Sw01 ∷ Toff234 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 0 2 (Sw12 ∷ Toff234 ∷ []) (sym (wl0140 c4)) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 c4)) ▸
       at 1 2 (Sw01 ∷ Toff234 ∷ []) (sym (c₂ (Swap) (Toff))) ▸ done


-- nat 0 BOX(1;32): 2 steps
lem-nat-0-BOX⟨1·32⟩ : WsL → ⟪ (Sw01 ∷ Bx1-32 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-32 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·32⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-32 ∷ []) (Bx0-32 ∷ Sw01 ∷ [])
  b0 = at 0 2 (Bx1-32 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ)) ▸
       at 0 1 (Bx0-32 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 BOX(3;142): 8 steps
lem-nat-0-BOX⟨3·142⟩ : WsL → ⟪ (Sw01 ∷ Bx3-142 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-042 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·142⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-142 ∷ []) (Bx3-042 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff314 ∷ Bx1-32 ∷ Toff314 ∷ CCZ134 ∷ Bx1-32 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 1 2 (Toff304 ∷ Sw01 ∷ []) (lem-nat-0-TOFF314 c4) ▸
       at 2 2 (Bx0-32 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·32⟩ c4) ▸
       at 3 2 (Toff304 ∷ Sw01 ∷ []) (lem-nat-0-TOFF314 c4) ▸
       at 4 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 5 2 (Bx0-32 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·32⟩ c4) ▸
       at 0 6 (Bx3-042 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;3042): 8 steps
lem-nat-0-BOX⟨1·3042⟩ : WsL → ⟪ (Sw01 ∷ Bx1-3042 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3142 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·3042⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-3042 ∷ []) (Bx0-3142 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff103 ∷ Bx3-142 ∷ Toff103 ∷ CCZ013 ∷ Bx3-142 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw01 ∷ []) (sym (wl0100 c4)) ▸
       at 1 2 (Toff013 ∷ Sw01 ∷ []) (wl0102 c4) ▸
       at 2 2 (Bx3-042 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·142⟩ c4) ▸
       at 3 2 (Toff013 ∷ Sw01 ∷ []) (wl0102 c4) ▸
       at 4 2 (CCZ013 ∷ Sw01 ∷ []) (sym (wl0100 c4)) ▸
       at 5 2 (Bx3-042 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·142⟩ c4) ▸
       at 0 6 (Bx0-3142 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;31): 3 steps
lem-nat-1-BOX⟨2·31⟩ : WsL → ⟪ (Sw12 ∷ Bx2-31 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-32 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·31⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-31 ∷ []) (Bx1-32 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ13 ∷ []) (refl) ▸
       at 0 2 (CZ23 ∷ Sw12 ∷ []) (sym (wl0029 c4)) ▸
       at 0 1 (Bx1-32 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;241): 8 steps
lem-nat-1-BOX⟨3·241⟩ : WsL → ⟪ (Sw12 ∷ Bx3-241 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-142 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·241⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-241 ∷ []) (Bx3-142 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff324 ∷ Bx2-31 ∷ Toff324 ∷ CCZ234 ∷ Bx2-31 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0034 c4)) ▸
       at 1 2 (Toff314 ∷ Sw12 ∷ []) (wl0063 c4) ▸
       at 2 2 (Bx1-32 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·31⟩ c4) ▸
       at 3 2 (Toff314 ∷ Sw12 ∷ []) (wl0063 c4) ▸
       at 4 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0034 c4)) ▸
       at 5 2 (Bx1-32 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·31⟩ c4) ▸
       at 0 6 (Bx3-142 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;3041): 8 steps
lem-nat-1-BOX⟨2·3041⟩ : WsL → ⟪ (Sw12 ∷ Bx2-3041 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3042 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·3041⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-3041 ∷ []) (Bx1-3042 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff203 ∷ Bx3-241 ∷ Toff203 ∷ CCZ023 ∷ Bx3-241 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 1 2 (Toff103 ∷ Sw12 ∷ []) (lem-nat-1-TOFF203 c4) ▸
       at 2 2 (Bx3-142 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·241⟩ c4) ▸
       at 3 2 (Toff103 ∷ Sw12 ∷ []) (lem-nat-1-TOFF203 c4) ▸
       at 4 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 5 2 (Bx3-142 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·241⟩ c4) ▸
       at 0 6 (Bx1-3042 ∷ []) (refl) ▸ done


-- nat 1 BOX(1;02): 3 steps
lem-nat-1-BOX⟨1·02⟩ : WsL → ⟪ (Sw12 ∷ Bx1-02 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-01 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·02⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-02 ∷ []) (Bx2-01 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ02 ∷ []) (refl) ▸
       at 0 2 (CZ01 ∷ Sw12 ∷ []) (lem-nat-1-CZ02 c4) ▸
       at 0 1 (Bx2-01 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;142): 8 steps
lem-nat-1-BOX⟨0·142⟩ : WsL → ⟪ (Sw12 ∷ Bx0-142 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-241 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·142⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-142 ∷ []) (Bx0-241 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff014 ∷ Bx1-02 ∷ Toff014 ∷ CCZ014 ∷ Bx1-02 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 1 2 (Toff024 ∷ Sw12 ∷ []) (lem-nat-1-TOFF014 c4) ▸
       at 2 2 (Bx2-01 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·02⟩ c4) ▸
       at 3 2 (Toff024 ∷ Sw12 ∷ []) (lem-nat-1-TOFF014 c4) ▸
       at 4 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 5 2 (Bx2-01 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·02⟩ c4) ▸
       at 0 6 (Bx0-241 ∷ []) (refl) ▸ done


-- nat 1 BOX(1;0342): 8 steps
lem-nat-1-BOX⟨1·0342⟩ : WsL → ⟪ (Sw12 ∷ Bx1-0342 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0341 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·0342⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-0342 ∷ []) (Bx2-0341 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff103 ∷ Bx0-142 ∷ Toff103 ∷ CCZ013 ∷ Bx0-142 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 1 2 (Toff203 ∷ Sw12 ∷ []) (lem-nat-1-TOFF103 c4) ▸
       at 2 2 (Bx0-241 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·142⟩ c4) ▸
       at 3 2 (Toff203 ∷ Sw12 ∷ []) (lem-nat-1-TOFF103 c4) ▸
       at 4 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 5 2 (Bx0-241 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·142⟩ c4) ▸
       at 0 6 (Bx2-0341 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;02): 3 steps
lem-nat-0-BOX⟨1·02⟩ : WsL → ⟪ (Sw01 ∷ Bx1-02 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-12 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·02⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-02 ∷ []) (Bx0-12 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ02 ∷ []) (refl) ▸
       at 0 2 (CZ12 ∷ Sw01 ∷ []) (sym (wl0137 c4)) ▸
       at 0 1 (Bx0-12 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;142): 8 steps
lem-nat-0-BOX⟨0·142⟩ : WsL → ⟪ (Sw01 ∷ Bx0-142 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-042 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·142⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-142 ∷ []) (Bx1-042 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff014 ∷ Bx1-02 ∷ Toff014 ∷ CCZ014 ∷ Bx1-02 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 1 2 (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 c4) ▸
       at 2 2 (Bx0-12 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·02⟩ c4) ▸
       at 3 2 (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 c4) ▸
       at 4 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 5 2 (Bx0-12 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·02⟩ c4) ▸
       at 0 6 (Bx1-042 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;0342): 8 steps
lem-nat-0-BOX⟨1·0342⟩ : WsL → ⟪ (Sw01 ∷ Bx1-0342 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1342 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·0342⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-0342 ∷ []) (Bx0-1342 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff103 ∷ Bx0-142 ∷ Toff103 ∷ CCZ013 ∷ Bx0-142 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw01 ∷ []) (sym (wl0100 c4)) ▸
       at 1 2 (Toff013 ∷ Sw01 ∷ []) (wl0102 c4) ▸
       at 2 2 (Bx1-042 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·142⟩ c4) ▸
       at 3 2 (Toff013 ∷ Sw01 ∷ []) (wl0102 c4) ▸
       at 4 2 (CCZ013 ∷ Sw01 ∷ []) (sym (wl0100 c4)) ▸
       at 5 2 (Bx1-042 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·142⟩ c4) ▸
       at 0 6 (Bx0-1342 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;01): 3 steps
lem-nat-1-BOX⟨2·01⟩ : WsL → ⟪ (Sw12 ∷ Bx2-01 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-02 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·01⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-01 ∷ []) (Bx1-02 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ01 ∷ []) (refl) ▸
       at 0 2 (CZ02 ∷ Sw12 ∷ []) (lem-nat-1-CZ01 c4) ▸
       at 0 1 (Bx1-02 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;241): 8 steps
lem-nat-1-BOX⟨0·241⟩ : WsL → ⟪ (Sw12 ∷ Bx0-241 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-142 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·241⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-241 ∷ []) (Bx0-142 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx2-01 ∷ Toff024 ∷ CCZ024 ∷ Bx2-01 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 1 2 (Toff014 ∷ Sw12 ∷ []) (lem-nat-1-TOFF024 c4) ▸
       at 2 2 (Bx1-02 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·01⟩ c4) ▸
       at 3 2 (Toff014 ∷ Sw12 ∷ []) (lem-nat-1-TOFF024 c4) ▸
       at 4 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 5 2 (Bx1-02 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·01⟩ c4) ▸
       at 0 6 (Bx0-142 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;0341): 8 steps
lem-nat-1-BOX⟨2·0341⟩ : WsL → ⟪ (Sw12 ∷ Bx2-0341 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0342 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·0341⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-0341 ∷ []) (Bx1-0342 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff203 ∷ Bx0-241 ∷ Toff203 ∷ CCZ023 ∷ Bx0-241 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 1 2 (Toff103 ∷ Sw12 ∷ []) (lem-nat-1-TOFF203 c4) ▸
       at 2 2 (Bx0-142 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·241⟩ c4) ▸
       at 3 2 (Toff103 ∷ Sw12 ∷ []) (lem-nat-1-TOFF203 c4) ▸
       at 4 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 5 2 (Bx0-142 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·241⟩ c4) ▸
       at 0 6 (Bx1-0342 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;124): 8 steps
lem-nat-0-BOX⟨0·124⟩ : WsL → ⟪ (Sw01 ∷ Bx0-124 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-024 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·124⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-124 ∷ []) (Bx1-024 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ Bx1-04 ∷ Toff012 ∷ CCZ012 ∷ Bx1-04 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 c4)) ▸
       at 1 2 (Toff102 ∷ Sw01 ∷ []) (wl0099 c4) ▸
       at 2 2 (Bx0-14 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·04⟩ c4) ▸
       at 3 2 (Toff102 ∷ Sw01 ∷ []) (wl0099 c4) ▸
       at 4 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 c4)) ▸
       at 5 2 (Bx0-14 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·04⟩ c4) ▸
       at 0 6 (Bx1-024 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;0324): 8 steps
lem-nat-0-BOX⟨1·0324⟩ : WsL → ⟪ (Sw01 ∷ Bx1-0324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·0324⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-0324 ∷ []) (Bx0-1324 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff103 ∷ Bx0-124 ∷ Toff103 ∷ CCZ013 ∷ Bx0-124 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw01 ∷ []) (sym (wl0100 c4)) ▸
       at 1 2 (Toff013 ∷ Sw01 ∷ []) (wl0102 c4) ▸
       at 2 2 (Bx1-024 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·124⟩ c4) ▸
       at 3 2 (Toff013 ∷ Sw01 ∷ []) (wl0102 c4) ▸
       at 4 2 (CCZ013 ∷ Sw01 ∷ []) (sym (wl0100 c4)) ▸
       at 5 2 (Bx1-024 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·124⟩ c4) ▸
       at 0 6 (Bx0-1324 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;214): 8 steps
lem-nat-1-BOX⟨0·214⟩ : WsL → ⟪ (Sw12 ∷ Bx0-214 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-124 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·214⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-214 ∷ []) (Bx0-124 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ Bx2-04 ∷ Toff012 ∷ CCZ012 ∷ Bx2-04 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 1 2 (Toff012 ∷ Sw12 ∷ []) (wl0038 c4) ▸
       at 2 2 (Bx1-04 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·04⟩ c4) ▸
       at 3 2 (Toff012 ∷ Sw12 ∷ []) (wl0038 c4) ▸
       at 4 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 5 2 (Bx1-04 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·04⟩ c4) ▸
       at 0 6 (Bx0-124 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;0314): 8 steps
lem-nat-1-BOX⟨2·0314⟩ : WsL → ⟪ (Sw12 ∷ Bx2-0314 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0324 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·0314⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-0314 ∷ []) (Bx1-0324 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff203 ∷ Bx0-214 ∷ Toff203 ∷ CCZ023 ∷ Bx0-214 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 1 2 (Toff103 ∷ Sw12 ∷ []) (lem-nat-1-TOFF203 c4) ▸
       at 2 2 (Bx0-124 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·214⟩ c4) ▸
       at 3 2 (Toff103 ∷ Sw12 ∷ []) (lem-nat-1-TOFF203 c4) ▸
       at 4 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 5 2 (Bx0-124 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·214⟩ c4) ▸
       at 0 6 (Bx1-0324 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;32): 2 steps
lem-nat-0-BOX⟨0·32⟩ : WsL → ⟪ (Sw01 ∷ Bx0-32 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-32 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·32⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-32 ∷ []) (Bx1-32 ∷ Sw01 ∷ [])
  b0 = at 0 2 (Bx0-32 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ)) ▸
       at 0 1 (Bx1-32 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 BOX(3;042): 8 steps
lem-nat-0-BOX⟨3·042⟩ : WsL → ⟪ (Sw01 ∷ Bx3-042 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-142 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·042⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-042 ∷ []) (Bx3-142 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff304 ∷ Bx0-32 ∷ Toff304 ∷ CCZ034 ∷ Bx0-32 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 1 2 (Toff314 ∷ Sw01 ∷ []) (lem-nat-0-TOFF304 c4) ▸
       at 2 2 (Bx1-32 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·32⟩ c4) ▸
       at 3 2 (Toff314 ∷ Sw01 ∷ []) (lem-nat-0-TOFF304 c4) ▸
       at 4 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 5 2 (Bx1-32 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·32⟩ c4) ▸
       at 0 6 (Bx3-142 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;3142): 8 steps
lem-nat-0-BOX⟨0·3142⟩ : WsL → ⟪ (Sw01 ∷ Bx0-3142 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3042 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·3142⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-3142 ∷ []) (Bx1-3042 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff013 ∷ Bx3-042 ∷ Toff013 ∷ CCZ013 ∷ Bx3-042 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw01 ∷ []) (sym (wl0100 c4)) ▸
       at 1 2 (Toff103 ∷ Sw01 ∷ []) (wl0101 c4) ▸
       at 2 2 (Bx3-142 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·042⟩ c4) ▸
       at 3 2 (Toff103 ∷ Sw01 ∷ []) (wl0101 c4) ▸
       at 4 2 (CCZ013 ∷ Sw01 ∷ []) (sym (wl0100 c4)) ▸
       at 5 2 (Bx3-142 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·042⟩ c4) ▸
       at 0 6 (Bx1-3042 ∷ []) (refl) ▸ done


-- nat 1 BOX(1;32): 3 steps
lem-nat-1-BOX⟨1·32⟩ : WsL → ⟪ (Sw12 ∷ Bx1-32 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-31 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·32⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-32 ∷ []) (Bx2-31 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ23 ∷ []) (refl) ▸
       at 0 2 (CZ13 ∷ Sw12 ∷ []) (sym (wl0026 c4)) ▸
       at 0 1 (Bx2-31 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;142): 8 steps
lem-nat-1-BOX⟨3·142⟩ : WsL → ⟪ (Sw12 ∷ Bx3-142 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-241 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·142⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-142 ∷ []) (Bx3-241 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff314 ∷ Bx1-32 ∷ Toff314 ∷ CCZ134 ∷ Bx1-32 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0084 c4)) ▸
       at 1 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 c4) ▸
       at 2 2 (Bx2-31 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·32⟩ c4) ▸
       at 3 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 c4) ▸
       at 4 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0084 c4)) ▸
       at 5 2 (Bx2-31 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·32⟩ c4) ▸
       at 0 6 (Bx3-241 ∷ []) (refl) ▸ done


-- nat 1 BOX(1;3042): 8 steps
lem-nat-1-BOX⟨1·3042⟩ : WsL → ⟪ (Sw12 ∷ Bx1-3042 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3041 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·3042⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-3042 ∷ []) (Bx2-3041 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff103 ∷ Bx3-142 ∷ Toff103 ∷ CCZ013 ∷ Bx3-142 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 1 2 (Toff203 ∷ Sw12 ∷ []) (lem-nat-1-TOFF103 c4) ▸
       at 2 2 (Bx3-241 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·142⟩ c4) ▸
       at 3 2 (Toff203 ∷ Sw12 ∷ []) (lem-nat-1-TOFF103 c4) ▸
       at 4 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 5 2 (Bx3-241 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·142⟩ c4) ▸
       at 0 6 (Bx2-3041 ∷ []) (refl) ▸ done


-- nat 3 TOFF412: 2 steps
lem-nat-3-TOFF412 : WsL → ⟪ (Sw34 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-TOFF412 c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Toff412 ∷ []) (Toff312 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Toff312 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0007 c4) ▸ done


-- nat 3 CS04: 2 steps
lem-nat-3-CS04 : WsL → ⟪ (Sw34 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-CS04 c4 = run b0
  where
  b0 : Chain (Sw34 ∷ CS04 ∷ []) (CS03 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0007 c4) ▸ done


-- nat 3 SBOX(2;0;4;1): 3 steps
lem-nat-3-SBOX⟨2·0·4·1⟩ : WsL → ⟪ (Sw34 ∷ Sb2-0-4-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-3-1 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨2·0·4·1⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb2-0-4-1 ∷ []) (Sb2-0-3-1 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS04 ∷ []) (refl) ▸
       at 0 2 (CS03 ∷ Sw34 ∷ []) (lem-nat-3-CS04 c4) ▸
       at 0 1 (Sb2-0-3-1 ∷ []) (refl) ▸ done


-- nat 3 CSd04: 2 steps
lem-nat-3-CSd04 : WsL → ⟪ (Sw34 ∷ CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-CSd04 c4 = run b0
  where
  b0 : Chain (Sw34 ∷ CS04⁻ ∷ []) (CS03⁻ ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CS03⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0007 c4) ▸ done


-- nat 3 SBOXd(2;0;4;1): 3 steps
lem-nat-3-SBOXd⟨2·0·4·1⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻2-0-4-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-3-1 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨2·0·4·1⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻2-0-4-1 ∷ []) (Sb⁻2-0-3-1 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS04⁻ ∷ []) (refl) ▸
       at 0 2 (CS03⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd04 c4) ▸
       at 0 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸ done


-- nat 3 SBOX(2;0;31;4): 7 steps
lem-nat-3-SBOX⟨2·0·31·4⟩ : WsL → ⟪ (Sw34 ∷ Sb2-0-31-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨2·0·31·4⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb2-0-31-4 ∷ []) (Sb2-0-41-3 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx2-0314 ∷ Toff413 ∷ Sb2-0-4-1 ∷ Toff413 ∷ Sb⁻2-0-4-1 ∷ []) (refl) ▸
       at 0 2 (Bx2-0413 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·0314⟩ c4) ▸
       at 1 2 (Toff314 ∷ Sw34 ∷ []) (wl0141 c4) ▸
       at 2 2 (Sb2-0-3-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·0·4·1⟩ c4) ▸
       at 3 2 (Toff314 ∷ Sw34 ∷ []) (wl0141 c4) ▸
       at 4 2 (Sb⁻2-0-3-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨2·0·4·1⟩ c4) ▸
       at 0 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done


-- nat 3 BOX(3;02): 2 steps
lem-nat-3-BOX⟨3·02⟩ : WsL → ⟪ (Sw34 ∷ Bx3-02 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-02 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨3·02⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx3-02 ∷ []) (Bx4-02 ∷ Sw34 ∷ [])
  b0 = at 0 2 (Bx3-02 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑ • CZ • Swap ↑) (Swap))) ▸
       at 0 1 (Bx4-02 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 BOX(0;312): 8 steps
lem-nat-3-BOX⟨0·312⟩ : WsL → ⟪ (Sw34 ∷ Bx0-312 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-412 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·312⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx0-312 ∷ []) (Bx0-412 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff013 ∷ Bx3-02 ∷ Toff013 ∷ CCZ013 ∷ Bx3-02 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 1 2 (Toff014 ∷ Sw34 ∷ []) (lem-nat-3-TOFF013 c4) ▸
       at 2 2 (Bx4-02 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·02⟩ c4) ▸
       at 3 2 (Toff014 ∷ Sw34 ∷ []) (lem-nat-3-TOFF013 c4) ▸
       at 4 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 5 2 (Bx4-02 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·02⟩ c4) ▸
       at 0 6 (Bx0-412 ∷ []) (refl) ▸ done


-- nat 3 BOX(3;0412): 8 steps
lem-nat-3-BOX⟨3·0412⟩ : WsL → ⟪ (Sw34 ∷ Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0312 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨3·0412⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx3-0412 ∷ []) (Bx4-0312 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff304 ∷ Bx0-312 ∷ Toff304 ∷ CCZ034 ∷ Bx0-312 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw34 ∷ []) (lem-nat-3-CCZ034 c4) ▸
       at 1 2 (Toff403 ∷ Sw34 ∷ []) (lem-nat-3-TOFF304 c4) ▸
       at 2 2 (Bx0-412 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·312⟩ c4) ▸
       at 3 2 (Toff403 ∷ Sw34 ∷ []) (lem-nat-3-TOFF304 c4) ▸
       at 4 2 (CCZ034 ∷ Sw34 ∷ []) (lem-nat-3-CCZ034 c4) ▸
       at 5 2 (Bx0-412 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·312⟩ c4) ▸
       at 0 6 (Bx4-0312 ∷ []) (refl) ▸ done


-- nat 3 SBOX(3;0;2;1): 2 steps
lem-nat-3-SBOX⟨3·0·2·1⟩ : WsL → ⟪ (Sw34 ∷ Sb3-0-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-0-2-1 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨3·0·2·1⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb3-0-2-1 ∷ []) (Sb4-0-2-1 ∷ Sw34 ∷ [])
  b0 = at 0 2 (Sb3-0-2-1 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑ • CS • Swap ↑) (Swap))) ▸
       at 0 1 (Sb4-0-2-1 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 SBOXd(3;0;2;1): 2 steps
lem-nat-3-SBOXd⟨3·0·2·1⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻3-0-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-0-2-1 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨3·0·2·1⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻3-0-2-1 ∷ []) (Sb⁻4-0-2-1 ∷ Sw34 ∷ [])
  b0 = at 0 2 (Sb⁻3-0-2-1 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (Swap))) ▸
       at 0 1 (Sb⁻4-0-2-1 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 SBOX(3;0;41;2): 7 steps
lem-nat-3-SBOX⟨3·0·41·2⟩ : WsL → ⟪ (Sw34 ∷ Sb3-0-41-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-0-31-2 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨3·0·41·2⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb3-0-41-2 ∷ []) (Sb4-0-31-2 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (refl) ▸
       at 0 2 (Bx4-0312 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·0412⟩ c4) ▸
       at 1 2 (Toff213 ∷ Sw34 ∷ []) (lem-nat-3-TOFF214 c4) ▸
       at 2 2 (Sb4-0-2-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨3·0·2·1⟩ c4) ▸
       at 3 2 (Toff213 ∷ Sw34 ∷ []) (lem-nat-3-TOFF214 c4) ▸
       at 4 2 (Sb⁻4-0-2-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨3·0·2·1⟩ c4) ▸
       at 0 5 (Sb4-0-31-2 ∷ []) (refl) ▸ done


-- nat 1 SBOX(1;0;4;2): 3 steps
lem-nat-1-SBOX⟨1·0·4·2⟩ : WsL → ⟪ (Sw12 ∷ Sb1-0-4-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-4-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨1·0·4·2⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb1-0-4-2 ∷ []) (Sb2-0-4-1 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS04 ∷ []) (refl) ▸
       at 0 2 (CS04 ∷ Sw12 ∷ []) (lem-nat-1-CS04 c4) ▸
       at 0 1 (Sb2-0-4-1 ∷ []) (refl) ▸ done


-- nat 1 CSd04: 5 steps
lem-nat-1-CSd04 : WsL → ⟪ (Sw12 ∷ CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS04⁻ ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-CSd04 c4 = run b0
  where
  b0 : Chain (Sw12 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CS03⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 1 2 (CS03⁻ ∷ Sw12 ∷ []) (sym (wl0023 c4)) ▸
       at 2 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 0 3 (CS04⁻ ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 1 SBOXd(1;0;4;2): 3 steps
lem-nat-1-SBOXd⟨1·0·4·2⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻1-0-4-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-4-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨1·0·4·2⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻1-0-4-2 ∷ []) (Sb⁻2-0-4-1 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS04⁻ ∷ []) (refl) ▸
       at 0 2 (CS04⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd04 c4) ▸
       at 0 1 (Sb⁻2-0-4-1 ∷ []) (refl) ▸ done


-- nat 1 SBOX(1;0;32;4): 7 steps
lem-nat-1-SBOX⟨1·0·32·4⟩ : WsL → ⟪ (Sw12 ∷ Sb1-0-32-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-31-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨1·0·32·4⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb1-0-32-4 ∷ []) (Sb2-0-31-4 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx1-0324 ∷ Toff423 ∷ Sb1-0-4-2 ∷ Toff423 ∷ Sb⁻1-0-4-2 ∷ []) (refl) ▸
       at 0 2 (Bx2-0314 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0324⟩ c4) ▸
       at 1 2 (Toff413 ∷ Sw12 ∷ []) (wl0091 c4) ▸
       at 2 2 (Sb2-0-4-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·4·2⟩ c4) ▸
       at 3 2 (Toff413 ∷ Sw12 ∷ []) (wl0091 c4) ▸
       at 4 2 (Sb⁻2-0-4-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·0·4·2⟩ c4) ▸
       at 0 5 (Sb2-0-31-4 ∷ []) (refl) ▸ done


-- nat 1 TOFF403: 134 steps
lem-nat-1-TOFF403 : WsL → ⟪ (Sw12 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-TOFF403 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (run b16))))))))))))))))
  where
  b0 : Chain (Sw12 ∷ Toff403 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Toff402 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw12 ∷ Toff401 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ Toff301 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (K3 ∷ Sw23 ∷ []) (sym (wl0057 c4)) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b1 = at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 7 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (K3 ∷ Sw23 ∷ []) (sym (wl0057 c4)) ▸
       at 11 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸ done

  b2 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b2 = at 12 2 [] (wl0006 c4) ▸
       at 3 2 (K4 ∷ Sw34 ∷ []) (sym (wl0067 c4)) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 4 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 6 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸ done

  b3 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Sw12 ∷ Sw23 ∷ K4 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw23 ∷ [])
  b3 = at 10 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 8 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K4 ∷ Sw34 ∷ []) (sym (wl0067 c4)) ▸
       at 10 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 11 2 [] (wl0007 c4) ▸
       at 2 2 (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑)) ▸
       at 3 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 c4)) ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸ done

  b4 : Chain (Sw12 ∷ Sw23 ∷ K4 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw23 ∷ []) (Sw12 ∷ Sw23 ∷ K4 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw23 ∷ [])
  b4 = at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS24⁻ ∷ Sw12 ∷ []) (sym (wl0009 c4)) ▸
       at 8 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 6 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 8 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸
       at 9 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸ done

  b5 : Chain (Sw12 ∷ Sw23 ∷ K4 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw23 ∷ []) (Sw12 ∷ K4 ∷ CS34 ∷ CX03 ∷ Sw23 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K4 ∷ ι ∷ Sw23 ∷ [])
  b5 = at 7 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑)) ▸
       at 9 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 10 2 [] (wl0001 c4) ▸
       at 1 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸
       at 2 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0011 c4)) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 3 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸ done

  b6 : Chain (Sw12 ∷ K4 ∷ CS34 ∷ CX03 ∷ Sw23 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K4 ∷ ι ∷ Sw23 ∷ []) (Sw12 ∷ K4 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ K4 ∷ ι ∷ Sw23 ∷ [])
  b6 = at 4 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0012 c4)) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 5 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0013 c4) ▸
       at 8 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 9 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 10 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸ done

  b7 : Chain (Sw12 ∷ K4 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ K4 ∷ ι ∷ Sw23 ∷ []) (K4 ∷ CS34 ∷ CX03 ∷ Sw12 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K4 ∷ ι ∷ [])
  b7 = at 11 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (sym (wl0013 c4)) ▸
       at 6 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 9 2 [] (wl0006 c4) ▸
       at 0 2 (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑)) ▸
       at 1 2 (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸
       at 2 2 (CX03 ∷ Sw12 ∷ []) (sym (wl0014 c4)) ▸ done

  b8 : Chain (K4 ∷ CS34 ∷ CX03 ∷ Sw12 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K4 ∷ ι ∷ []) (K4 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K4 ∷ Sw12 ∷ ι ∷ [])
  b8 = at 3 2 (CS34⁻ ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS • CS • CS)) ▸
       at 4 2 (CX03 ∷ Sw12 ∷ []) (sym (wl0014 c4)) ▸
       at 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 6 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸
       at 7 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 5 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑)) ▸ done

  b9 : Chain (K4 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K4 ∷ Sw12 ∷ ι ∷ []) (Sw23 ∷ K4 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ Sw23 ∷ Sw23 ∷ CX02 ∷ Sw23 ∷ CS04 ∷ K4 ∷ ι ∷ Sw12 ∷ [])
  b9 = at 7 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 1 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸
       at 2 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0015 c4)) ▸
       at 4 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0006 c4) ▸
       at 4 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0016 c4)) ▸
       at 6 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b10 : Chain (Sw23 ∷ K4 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ Sw23 ∷ Sw23 ∷ CX02 ∷ Sw23 ∷ CS04 ∷ K4 ∷ ι ∷ Sw12 ∷ []) (Sw23 ∷ K4 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ Sw23 ∷ K4 ∷ ι ∷ Sw12 ∷ [])
  b10 = at 5 2 [] (wl0006 c4) ▸
       at 7 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0013 c4) ▸
       at 8 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 9 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 10 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 11 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (sym (wl0013 c4)) ▸
       at 6 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done

  b11 : Chain (Sw23 ∷ K4 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ Sw23 ∷ K4 ∷ ι ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ Sw12 ∷ CX02 ∷ CS04 ∷ K4 ∷ ι ∷ Sw23 ∷ Sw12 ∷ [])
  b11 = at 7 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 2 2 (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑)) ▸
       at 3 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0017 c4)) ▸
       at 5 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0001 c4) ▸
       at 5 2 (CS14⁻ ∷ Sw12 ∷ []) (sym (wl0018 c4)) ▸ done

  b12 : Chain (Sw23 ∷ Sw12 ∷ K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ Sw12 ∷ CX02 ∷ CS04 ∷ K4 ∷ ι ∷ Sw23 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K4 ∷ Sw12 ∷ ι ∷ Sw23 ∷ Sw12 ∷ [])
  b12 = at 7 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0001 c4) ▸
       at 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 8 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸
       at 9 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 7 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑)) ▸ done

  b13 : Chain (Sw23 ∷ Sw12 ∷ K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K4 ∷ Sw12 ∷ ι ∷ Sw23 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw34 ∷ CX01 ∷ CS04 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ [])
  b13 = at 9 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 3 2 (K3 ∷ Sw34 ∷ []) (sym (wl0068 c4)) ▸
       at 5 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0007 c4) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0007 c4) ▸ done

  b14 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw34 ∷ CX01 ∷ CS04 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K2 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ [])
  b14 = at 7 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 9 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0007 c4) ▸
       at 9 2 (K3 ∷ Sw34 ∷ []) (sym (wl0068 c4)) ▸
       at 10 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 4 2 (K2 ∷ Sw23 ∷ []) (sym (wl0058 c4)) ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b15 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K2 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ Sw23 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ [])
  b15 = at 5 2 [] (wl0006 c4) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0006 c4) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (wl0006 c4) ▸
       at 10 2 (K2 ∷ Sw23 ∷ []) (sym (wl0058 c4)) ▸ done

  b16 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ Sw23 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Toff403 ∷ Sw12 ∷ [])
  b16 = at 11 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 4 8 (Toff201 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (Toff301 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff401 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff402 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff403 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 1 BOX(4;02): 3 steps
lem-nat-1-BOX⟨4·02⟩ : WsL → ⟪ (Sw12 ∷ Bx4-02 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-01 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·02⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-02 ∷ []) (Bx4-01 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ02 ∷ []) (refl) ▸
       at 0 2 (CZ01 ∷ Sw12 ∷ []) (lem-nat-1-CZ02 c4) ▸
       at 0 1 (Bx4-01 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;412): 8 steps
lem-nat-1-BOX⟨0·412⟩ : WsL → ⟪ (Sw12 ∷ Bx0-412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-421 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·412⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-412 ∷ []) (Bx0-421 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff014 ∷ Bx4-02 ∷ Toff014 ∷ CCZ014 ∷ Bx4-02 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 1 2 (Toff024 ∷ Sw12 ∷ []) (lem-nat-1-TOFF014 c4) ▸
       at 2 2 (Bx4-01 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·02⟩ c4) ▸
       at 3 2 (Toff024 ∷ Sw12 ∷ []) (lem-nat-1-TOFF014 c4) ▸
       at 4 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 5 2 (Bx4-01 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·02⟩ c4) ▸
       at 0 6 (Bx0-421 ∷ []) (refl) ▸ done


-- nat 1 BOX(4;0312): 8 steps
lem-nat-1-BOX⟨4·0312⟩ : WsL → ⟪ (Sw12 ∷ Bx4-0312 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0321 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·0312⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-0312 ∷ []) (Bx4-0321 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff403 ∷ Bx0-412 ∷ Toff403 ∷ CCZ034 ∷ Bx0-412 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 1 2 (Toff403 ∷ Sw12 ∷ []) (lem-nat-1-TOFF403 c4) ▸
       at 2 2 (Bx0-421 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·412⟩ c4) ▸
       at 3 2 (Toff403 ∷ Sw12 ∷ []) (lem-nat-1-TOFF403 c4) ▸
       at 4 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 5 2 (Bx0-421 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·412⟩ c4) ▸
       at 0 6 (Bx4-0321 ∷ []) (refl) ▸ done


-- nat 1 SBOX(4;0;2;1): 3 steps
lem-nat-1-SBOX⟨4·0·2·1⟩ : WsL → ⟪ (Sw12 ∷ Sb4-0-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-0-1-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨4·0·2·1⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb4-0-2-1 ∷ []) (Sb4-0-1-2 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS02 ∷ []) (refl) ▸
       at 0 2 (CS01 ∷ Sw12 ∷ []) (lem-nat-1-CS02 c4) ▸
       at 0 1 (Sb4-0-1-2 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(4;0;2;1): 3 steps
lem-nat-1-SBOXd⟨4·0·2·1⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻4-0-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-0-1-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨4·0·2·1⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻4-0-2-1 ∷ []) (Sb⁻4-0-1-2 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS02⁻ ∷ []) (refl) ▸
       at 0 2 (CS01⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd02 c4) ▸
       at 0 1 (Sb⁻4-0-1-2 ∷ []) (refl) ▸ done


-- nat 1 SBOX(4;0;31;2): 7 steps
lem-nat-1-SBOX⟨4·0·31·2⟩ : WsL → ⟪ (Sw12 ∷ Sb4-0-31-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-0-32-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨4·0·31·2⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb4-0-31-2 ∷ []) (Sb4-0-32-1 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx4-0312 ∷ Toff213 ∷ Sb4-0-2-1 ∷ Toff213 ∷ Sb⁻4-0-2-1 ∷ []) (refl) ▸
       at 0 2 (Bx4-0321 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0312⟩ c4) ▸
       at 1 2 (Toff123 ∷ Sw12 ∷ []) (wl0112 c4) ▸
       at 2 2 (Sb4-0-1-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨4·0·2·1⟩ c4) ▸
       at 3 2 (Toff123 ∷ Sw12 ∷ []) (wl0112 c4) ▸
       at 4 2 (Sb⁻4-0-1-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨4·0·2·1⟩ c4) ▸
       at 0 5 (Sb4-0-32-1 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;04): 3 steps
lem-nat-2-BOX⟨1·04⟩ : WsL → ⟪ (Sw23 ∷ Bx1-04 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-04 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·04⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-04 ∷ []) (Bx1-04 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ04 ∷ []) (refl) ▸
       at 0 2 (CZ04 ∷ Sw23 ∷ []) (lem-nat-2-CZ04 c4) ▸
       at 0 1 (Bx1-04 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;134): 8 steps
lem-nat-2-BOX⟨0·134⟩ : WsL → ⟪ (Sw23 ∷ Bx0-134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-124 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·134⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-134 ∷ []) (Bx0-124 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff013 ∷ Bx1-04 ∷ Toff013 ∷ CCZ013 ∷ Bx1-04 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 1 2 (Toff012 ∷ Sw23 ∷ []) (lem-nat-2-TOFF013 c4) ▸
       at 2 2 (Bx1-04 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·04⟩ c4) ▸
       at 3 2 (Toff012 ∷ Sw23 ∷ []) (lem-nat-2-TOFF013 c4) ▸
       at 4 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 5 2 (Bx1-04 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·04⟩ c4) ▸
       at 0 6 (Bx0-124 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;0234): 8 steps
lem-nat-2-BOX⟨1·0234⟩ : WsL → ⟪ (Sw23 ∷ Bx1-0234 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0324 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·0234⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-0234 ∷ []) (Bx1-0324 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff102 ∷ Bx0-134 ∷ Toff102 ∷ CCZ012 ∷ Bx0-134 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 1 2 (Toff103 ∷ Sw23 ∷ []) (lem-nat-2-TOFF102 c4) ▸
       at 2 2 (Bx0-124 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·134⟩ c4) ▸
       at 3 2 (Toff103 ∷ Sw23 ∷ []) (lem-nat-2-TOFF102 c4) ▸
       at 4 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 5 2 (Bx0-124 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·134⟩ c4) ▸
       at 0 6 (Bx1-0324 ∷ []) (refl) ▸ done


-- nat 2 CS04: 7 steps
lem-nat-2-CS04 : WsL → ⟪ (Sw23 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-CS04 c4 = run b0
  where
  b0 : Chain (Sw23 ∷ CS04 ∷ []) (CS04 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0013 c4) ▸
       at 2 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 3 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 4 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 5 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (sym (wl0013 c4)) ▸
       at 0 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 SBOX(1;0;4;3): 3 steps
lem-nat-2-SBOX⟨1·0·4·3⟩ : WsL → ⟪ (Sw23 ∷ Sb1-0-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-4-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨1·0·4·3⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb1-0-4-3 ∷ []) (Sb1-0-4-2 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS04 ∷ []) (refl) ▸
       at 0 2 (CS04 ∷ Sw23 ∷ []) (lem-nat-2-CS04 c4) ▸
       at 0 1 (Sb1-0-4-2 ∷ []) (refl) ▸ done


-- nat 2 CSd04: 7 steps
lem-nat-2-CSd04 : WsL → ⟪ (Sw23 ∷ CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS04⁻ ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-CSd04 c4 = run b0
  where
  b0 : Chain (Sw23 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0013 c4) ▸
       at 2 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 3 2 (CS01⁻ ∷ Sw34 ∷ []) (sym (c₂ (CS • CS • CS) (Swap ↑))) ▸
       at 4 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 5 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (sym (wl0013 c4)) ▸
       at 0 7 (CS04⁻ ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 SBOXd(1;0;4;3): 3 steps
lem-nat-2-SBOXd⟨1·0·4·3⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻1-0-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-4-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨1·0·4·3⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻1-0-4-3 ∷ []) (Sb⁻1-0-4-2 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS04⁻ ∷ []) (refl) ▸
       at 0 2 (CS04⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd04 c4) ▸
       at 0 1 (Sb⁻1-0-4-2 ∷ []) (refl) ▸ done


-- nat 2 SBOX(1;0;23;4): 7 steps
lem-nat-2-SBOX⟨1·0·23·4⟩ : WsL → ⟪ (Sw23 ∷ Sb1-0-23-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-32-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨1·0·23·4⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb1-0-23-4 ∷ []) (Sb1-0-32-4 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx1-0234 ∷ Toff423 ∷ Sb1-0-4-3 ∷ Toff423 ∷ Sb⁻1-0-4-3 ∷ []) (refl) ▸
       at 0 2 (Bx1-0324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0234⟩ c4) ▸
       at 1 2 (Toff423 ∷ Sw23 ∷ []) (wl0087 c4) ▸
       at 2 2 (Sb1-0-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·4·3⟩ c4) ▸
       at 3 2 (Toff423 ∷ Sw23 ∷ []) (wl0087 c4) ▸
       at 4 2 (Sb⁻1-0-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·4·3⟩ c4) ▸
       at 0 5 (Sb1-0-32-4 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;421): 8 steps
lem-nat-2-BOX⟨0·421⟩ : WsL → ⟪ (Sw23 ∷ Bx0-421 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-431 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·421⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-421 ∷ []) (Bx0-431 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx4-01 ∷ Toff024 ∷ CCZ024 ∷ Bx4-01 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 1 2 (Toff034 ∷ Sw23 ∷ []) (lem-nat-2-TOFF024 c4) ▸
       at 2 2 (Bx4-01 ∷ Sw23 ∷ []) (sym (c₂ (CZ) (Swap))) ▸
       at 3 2 (Toff034 ∷ Sw23 ∷ []) (lem-nat-2-TOFF024 c4) ▸
       at 4 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 5 2 (Bx4-01 ∷ Sw23 ∷ []) (sym (c₂ (CZ) (Swap))) ▸
       at 0 6 (Bx0-431 ∷ []) (refl) ▸ done


-- nat 2 BOX(4;0321): 8 steps
lem-nat-2-BOX⟨4·0321⟩ : WsL → ⟪ (Sw23 ∷ Bx4-0321 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0231 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·0321⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-0321 ∷ []) (Bx4-0231 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff403 ∷ Bx0-421 ∷ Toff403 ∷ CCZ034 ∷ Bx0-421 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 1 2 (Toff402 ∷ Sw23 ∷ []) (lem-nat-2-TOFF403 c4) ▸
       at 2 2 (Bx0-431 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·421⟩ c4) ▸
       at 3 2 (Toff402 ∷ Sw23 ∷ []) (lem-nat-2-TOFF403 c4) ▸
       at 4 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 5 2 (Bx0-431 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·421⟩ c4) ▸
       at 0 6 (Bx4-0231 ∷ []) (refl) ▸ done


-- nat 2 SBOX(4;0;1;2): 2 steps
lem-nat-2-SBOX⟨4·0·1·2⟩ : WsL → ⟪ (Sw23 ∷ Sb4-0-1-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-0-1-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨4·0·1·2⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb4-0-1-2 ∷ []) (Sb4-0-1-3 ∷ Sw23 ∷ [])
  b0 = at 0 2 (Sb4-0-1-2 ∷ Sw23 ∷ []) (sym (c₂ (CS) (Swap))) ▸
       at 0 1 (Sb4-0-1-3 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 SBOXd(4;0;1;2): 2 steps
lem-nat-2-SBOXd⟨4·0·1·2⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻4-0-1-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-0-1-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨4·0·1·2⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻4-0-1-2 ∷ []) (Sb⁻4-0-1-3 ∷ Sw23 ∷ [])
  b0 = at 0 2 (Sb⁻4-0-1-2 ∷ Sw23 ∷ []) (sym (c₂ (CS • CS • CS) (Swap))) ▸
       at 0 1 (Sb⁻4-0-1-3 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 SBOX(4;0;32;1): 7 steps
lem-nat-2-SBOX⟨4·0·32·1⟩ : WsL → ⟪ (Sw23 ∷ Sb4-0-32-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-0-23-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨4·0·32·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb4-0-32-1 ∷ []) (Sb4-0-23-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx4-0321 ∷ Toff123 ∷ Sb4-0-1-2 ∷ Toff123 ∷ Sb⁻4-0-1-2 ∷ []) (refl) ▸
       at 0 2 (Bx4-0231 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0321⟩ c4) ▸
       at 1 2 (Toff123 ∷ Sw23 ∷ []) (wl0114 c4) ▸
       at 2 2 (Sb4-0-1-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨4·0·1·2⟩ c4) ▸
       at 3 2 (Toff123 ∷ Sw23 ∷ []) (wl0114 c4) ▸
       at 4 2 (Sb⁻4-0-1-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨4·0·1·2⟩ c4) ▸
       at 0 5 (Sb4-0-23-1 ∷ []) (refl) ▸ done


-- nat 0 SBOX(0;1;4;3): 3 steps
lem-nat-0-SBOX⟨0·1·4·3⟩ : WsL → ⟪ (Sw01 ∷ Sb0-1-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-4-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨0·1·4·3⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb0-1-4-3 ∷ []) (Sb1-0-4-3 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS14 ∷ []) (refl) ▸
       at 0 2 (CS04 ∷ Sw01 ∷ []) (lem-nat-0-CS14 c4) ▸
       at 0 1 (Sb1-0-4-3 ∷ []) (refl) ▸ done


-- nat 0 CSd14: 5 steps
lem-nat-0-CSd14 : WsL → ⟪ (Sw01 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS04⁻ ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-CSd14 c4 = run b0
  where
  b0 : Chain (Sw01 ∷ CS14⁻ ∷ []) (CS04⁻ ∷ Sw01 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 1 2 (CS03⁻ ∷ Sw01 ∷ []) (sym (wl0022 c4)) ▸
       at 2 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 0 3 (CS04⁻ ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 SBOXd(0;1;4;3): 3 steps
lem-nat-0-SBOXd⟨0·1·4·3⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻0-1-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-4-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨0·1·4·3⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻0-1-4-3 ∷ []) (Sb⁻1-0-4-3 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS14⁻ ∷ []) (refl) ▸
       at 0 2 (CS04⁻ ∷ Sw01 ∷ []) (lem-nat-0-CSd14 c4) ▸
       at 0 1 (Sb⁻1-0-4-3 ∷ []) (refl) ▸ done


-- nat 0 SBOX(0;1;23;4): 7 steps
lem-nat-0-SBOX⟨0·1·23·4⟩ : WsL → ⟪ (Sw01 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-23-4 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨0·1·23·4⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb0-1-23-4 ∷ []) (Sb1-0-23-4 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 0 2 (Bx1-0234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1234⟩ c4) ▸
       at 1 2 (Toff423 ∷ Sw01 ∷ []) (c₂ (Swap) (Toffᵗ)) ▸
       at 2 2 (Sb1-0-4-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·4·3⟩ c4) ▸
       at 3 2 (Toff423 ∷ Sw01 ∷ []) (c₂ (Swap) (Toffᵗ)) ▸
       at 4 2 (Sb⁻1-0-4-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·4·3⟩ c4) ▸
       at 0 5 (Sb1-0-23-4 ∷ []) (refl) ▸ done


-- nat 0 BOX(4;01): 3 steps
lem-nat-0-BOX⟨4·01⟩ : WsL → ⟪ (Sw01 ∷ Bx4-01 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-10 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·01⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-01 ∷ []) (Bx4-10 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ01 ∷ []) (refl) ▸
       at 0 2 (CZ01 ∷ Sw01 ∷ []) (sym (wl0130 c4)) ▸
       at 0 1 (Bx4-10 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;431): 8 steps
lem-nat-0-BOX⟨0·431⟩ : WsL → ⟪ (Sw01 ∷ Bx0-431 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-430 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·431⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-431 ∷ []) (Bx1-430 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff034 ∷ Bx4-01 ∷ Toff034 ∷ CCZ034 ∷ Bx4-01 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 1 2 (Toff134 ∷ Sw01 ∷ []) (lem-nat-0-TOFF034 c4) ▸
       at 2 2 (Bx4-10 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·01⟩ c4) ▸
       at 3 2 (Toff134 ∷ Sw01 ∷ []) (lem-nat-0-TOFF034 c4) ▸
       at 4 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 5 2 (Bx4-10 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·01⟩ c4) ▸
       at 0 6 (Bx1-430 ∷ []) (refl) ▸ done


-- nat 0 BOX(4;0231): 8 steps
lem-nat-0-BOX⟨4·0231⟩ : WsL → ⟪ (Sw01 ∷ Bx4-0231 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1230 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·0231⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-0231 ∷ []) (Bx4-1230 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff402 ∷ Bx0-431 ∷ Toff402 ∷ CCZ024 ∷ Bx0-431 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 1 2 (Toff412 ∷ Sw01 ∷ []) (lem-nat-0-TOFF402 c4) ▸
       at 2 2 (Bx1-430 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·431⟩ c4) ▸
       at 3 2 (Toff412 ∷ Sw01 ∷ []) (lem-nat-0-TOFF402 c4) ▸
       at 4 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 5 2 (Bx1-430 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·431⟩ c4) ▸
       at 0 6 (Bx4-1230 ∷ []) (refl) ▸ done


-- nat 0 SBOX(4;0;1;3): 3 steps
lem-nat-0-SBOX⟨4·0·1·3⟩ : WsL → ⟪ (Sw01 ∷ Sb4-0-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-1-0-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨4·0·1·3⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb4-0-1-3 ∷ []) (Sb4-1-0-3 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS01 ∷ []) (refl) ▸
       at 0 2 (CS01 ∷ Sw01 ∷ []) (sym (wl0132 c4)) ▸
       at 0 1 (Sb4-1-0-3 ∷ []) (refl) ▸ done


-- nat 0 SBOXd(4;0;1;3): 3 steps
lem-nat-0-SBOXd⟨4·0·1·3⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻4-0-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-1-0-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨4·0·1·3⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻4-0-1-3 ∷ []) (Sb⁻4-1-0-3 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS01⁻ ∷ []) (refl) ▸
       at 0 2 (CS01⁻ ∷ Sw01 ∷ []) (sym (wl0133 c4)) ▸
       at 0 1 (Sb⁻4-1-0-3 ∷ []) (refl) ▸ done


-- nat 0 SBOX(4;0;23;1): 7 steps
lem-nat-0-SBOX⟨4·0·23·1⟩ : WsL → ⟪ (Sw01 ∷ Sb4-0-23-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-1-23-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨4·0·23·1⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb4-0-23-1 ∷ []) (Sb4-1-23-0 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx4-0231 ∷ Toff123 ∷ Sb4-0-1-3 ∷ Toff123 ∷ Sb⁻4-0-1-3 ∷ []) (refl) ▸
       at 0 2 (Bx4-1230 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·0231⟩ c4) ▸
       at 1 2 (Toff023 ∷ Sw01 ∷ []) (wl0053 c4) ▸
       at 2 2 (Sb4-1-0-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨4·0·1·3⟩ c4) ▸
       at 3 2 (Toff023 ∷ Sw01 ∷ []) (wl0053 c4) ▸
       at 4 2 (Sb⁻4-1-0-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨4·0·1·3⟩ c4) ▸
       at 0 5 (Sb4-1-23-0 ∷ []) (refl) ▸ done


-- nat 3 TOFF401: 2 steps
lem-nat-3-TOFF401 : WsL → ⟪ (Sw34 ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-TOFF401 c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Toff401 ∷ []) (Toff301 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Toff301 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0007 c4) ▸ done


-- nat 3 TOFF024: 80 steps
lem-nat-3-TOFF024 : WsL → ⟪ (Sw34 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-TOFF024 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (run b9)))))))))
  where
  b0 : Chain (Sw34 ∷ Toff024 ∷ []) (Sw34 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Toff014 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸ done

  b1 : Chain (Sw34 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) (Sw34 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ [])
  b1 = at 8 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 10 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 11 2 [] (wl0006 c4) ▸ done

  b2 : Chain (Sw34 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ []) (Sw34 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ [])
  b2 = at 2 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 3 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 5 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 9 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸ done

  b3 : Chain (Sw34 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ []) (Sw34 ∷ K0 ∷ CS24 ∷ CX02 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ [])
  b3 = at 7 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 9 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 10 2 [] (wl0007 c4) ▸
       at 1 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 2 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 c4)) ▸
       at 5 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 3 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (Sw34 ∷ K0 ∷ CS24 ∷ CX02 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ []) (Sw34 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ Sw12 ∷ K0 ∷ ι ∷ Sw12 ∷ [])
  b4 = at 4 2 (CS24⁻ ∷ Sw12 ∷ []) (sym (wl0009 c4)) ▸
       at 7 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 5 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 7 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸
       at 8 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done

  b5 : Chain (Sw34 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ Sw12 ∷ K0 ∷ ι ∷ Sw12 ∷ []) (K0 ∷ CS23 ∷ CX02 ∷ Sw34 ∷ Sw34 ∷ CS23⁻ ∷ Sw34 ∷ CX02 ∷ CS04 ∷ K0 ∷ ι ∷ [])
  b5 = at 7 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 8 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 9 2 [] (wl0001 c4) ▸
       at 0 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 2 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0007 c4) ▸
       at 2 2 (CX02 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap))) ▸
       at 4 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b6 : Chain (K0 ∷ CS23 ∷ CX02 ∷ Sw34 ∷ Sw34 ∷ CS23⁻ ∷ Sw34 ∷ CX02 ∷ CS04 ∷ K0 ∷ ι ∷ []) (Sw12 ∷ K0 ∷ Sw12 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ [])
  b6 = at 3 2 [] (wl0007 c4) ▸
       at 4 2 (CX02 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap))) ▸
       at 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0007 c4) ▸
       at 6 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 7 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 1 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸ done

  b7 : Chain (Sw12 ∷ K0 ∷ Sw12 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ []) (Sw12 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ Sw12 ∷ ι ∷ Sw34 ∷ [])
  b7 = at 2 2 (CS13 ∷ Sw12 ∷ []) (sym (wl0024 c4)) ▸
       at 4 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0001 c4) ▸
       at 4 2 (CS13⁻ ∷ Sw12 ∷ []) (sym (wl0043 c4)) ▸
       at 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0001 c4) ▸
       at 6 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸
       at 7 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸ done

  b8 : Chain (Sw12 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ Sw12 ∷ ι ∷ Sw34 ∷ []) (Sw12 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw34 ∷ [])
  b8 = at 8 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 2 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0006 c4) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0006 c4) ▸ done

  b9 : Chain (Sw12 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw34 ∷ []) (Toff023 ∷ Sw34 ∷ [])
  b9 = at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0006 c4) ▸
       at 8 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 2 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff023 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 BOX(4;03): 3 steps
lem-nat-3-BOX⟨4·03⟩ : WsL → ⟪ (Sw34 ∷ Bx4-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-04 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨4·03⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx4-03 ∷ []) (Bx3-04 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ03 ∷ []) (refl) ▸
       at 0 2 (CZ04 ∷ Sw34 ∷ []) (lem-nat-3-CZ03 c4) ▸
       at 0 1 (Bx3-04 ∷ []) (refl) ▸ done


-- nat 3 BOX(0;423): 8 steps
lem-nat-3-BOX⟨0·423⟩ : WsL → ⟪ (Sw34 ∷ Bx0-423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-324 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·423⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx0-423 ∷ []) (Bx0-324 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx4-03 ∷ Toff024 ∷ CCZ024 ∷ Bx4-03 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 1 2 (Toff023 ∷ Sw34 ∷ []) (lem-nat-3-TOFF024 c4) ▸
       at 2 2 (Bx3-04 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·03⟩ c4) ▸
       at 3 2 (Toff023 ∷ Sw34 ∷ []) (lem-nat-3-TOFF024 c4) ▸
       at 4 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 5 2 (Bx3-04 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·03⟩ c4) ▸
       at 0 6 (Bx0-324 ∷ []) (refl) ▸ done


-- nat 3 BOX(4;0123): 8 steps
lem-nat-3-BOX⟨4·0123⟩ : WsL → ⟪ (Sw34 ∷ Bx4-0123 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨4·0123⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx4-0123 ∷ []) (Bx3-0124 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff401 ∷ Bx0-423 ∷ Toff401 ∷ CCZ014 ∷ Bx0-423 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 1 2 (Toff301 ∷ Sw34 ∷ []) (lem-nat-3-TOFF401 c4) ▸
       at 2 2 (Bx0-324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·423⟩ c4) ▸
       at 3 2 (Toff301 ∷ Sw34 ∷ []) (lem-nat-3-TOFF401 c4) ▸
       at 4 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 5 2 (Bx0-324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·423⟩ c4) ▸
       at 0 6 (Bx3-0124 ∷ []) (refl) ▸ done


-- nat 3 BOX(3;04): 3 steps
lem-nat-3-BOX⟨3·04⟩ : WsL → ⟪ (Sw34 ∷ Bx3-04 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-03 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨3·04⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx3-04 ∷ []) (Bx4-03 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ04 ∷ []) (refl) ▸
       at 0 2 (CZ03 ∷ Sw34 ∷ []) (lem-nat-3-CZ04 c4) ▸
       at 0 1 (Bx4-03 ∷ []) (refl) ▸ done


-- nat 3 BOX(0;324): 8 steps
lem-nat-3-BOX⟨0·324⟩ : WsL → ⟪ (Sw34 ∷ Bx0-324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-423 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·324⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx0-324 ∷ []) (Bx0-423 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4) ▸
       at 1 2 (Toff024 ∷ Sw34 ∷ []) (lem-nat-3-TOFF023 c4) ▸
       at 2 2 (Bx4-03 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·04⟩ c4) ▸
       at 3 2 (Toff024 ∷ Sw34 ∷ []) (lem-nat-3-TOFF023 c4) ▸
       at 4 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4) ▸
       at 5 2 (Bx4-03 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·04⟩ c4) ▸
       at 0 6 (Bx0-423 ∷ []) (refl) ▸ done


-- nat 3 BOX(3;0124): 8 steps
lem-nat-3-BOX⟨3·0124⟩ : WsL → ⟪ (Sw34 ∷ Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0123 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨3·0124⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx3-0124 ∷ []) (Bx4-0123 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff301 ∷ Bx0-324 ∷ Toff301 ∷ CCZ013 ∷ Bx0-324 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 1 2 (Toff401 ∷ Sw34 ∷ []) (lem-nat-3-TOFF301 c4) ▸
       at 2 2 (Bx0-423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·324⟩ c4) ▸
       at 3 2 (Toff401 ∷ Sw34 ∷ []) (lem-nat-3-TOFF301 c4) ▸
       at 4 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 5 2 (Bx0-423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·324⟩ c4) ▸
       at 0 6 (Bx4-0123 ∷ []) (refl) ▸ done


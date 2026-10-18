{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R008 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL ; wl0001 ; wl0003 ; wl0004 ; wl0005 ; wl0006 ; wl0007 ; wl0008 ; wl0009 ; wl0010 ; wl0011 ; wl0012 ; wl0013 ; wl0014 ; wl0016 ; wl0017 ; wl0023 ; wl0024 ; wl0025 ; wl0026 ; wl0027 ; wl0028 ; wl0035 ; wl0038 ; wl0039 ; wl0045 ; wl0046 ; wl0048 ; wl0053 ; wl0063 ; wl0064 ; wl0065 ; wl0066 ; wl0067 ; wl0068 ; wl0073 ; wl0076 ; wl0109 ; wl0115 ; wl0117 ; wl0118 ; wl0119 ; wl0121 ; wl0122 ; wl0123 ; wl0124 ; wl0125 ; wl0126 ; wl0127 ; wl0134 ; wl0135 ; wl0136 ; wl0137 ; wl0138 ; wl0139 ; wl0140 ; wl0141 ; wl0142)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-push-CS04-sw1-R ; lem-comm-push-CS04-sw2-R)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-comm-push-CCZ014-sw0-R ; lem-comm-push-CCZ014-sw2-R ; lem-comm-push-CS04-sw0-R ; lem-comm-push-CS14-sw0-R ; lem-comm-push-CSd14-sw0-R)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-comm-push-CCZ034-sw1-R)
-- comm push TOFF034 sw1 R: 110 steps
lem-comm-push-TOFF034-sw1-R : WsL → ⟪ (Sw12 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-TOFF034-sw1-R c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (run b13)))))))))))))
  where
  b0 : Chain (Sw12 ∷ Toff034 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Toff024 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw12 ∷ Toff014 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b1 = at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 7 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 11 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸ done

  b2 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b2 = at 12 2 [] (wl0003 c4) ▸
       at 3 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 4 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 6 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸ done

  b3 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Sw12 ∷ Sw23 ∷ K0 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ [])
  b3 = at 10 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 8 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 10 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 11 2 [] (wl0004 c4) ▸
       at 2 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 3 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0005 c4)) ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸ done

  b4 : Chain (Sw12 ∷ Sw23 ∷ K0 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ []) (Sw12 ∷ Sw23 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0 ∷ ι ∷ Sw23 ∷ [])
  b4 = at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS24⁻ ∷ Sw12 ∷ []) (sym (wl0007 c4)) ▸
       at 8 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 6 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R c4) ▸
       at 8 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 9 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 10 2 [] (wl0006 c4) ▸ done

  b5 : Chain (Sw12 ∷ Sw23 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0 ∷ ι ∷ Sw23 ∷ []) (Sw12 ∷ K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw23 ∷ [])
  b5 = at 1 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 2 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0008 c4)) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 3 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0009 c4)) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 5 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS04 ∷ Sw23 ∷ []) (lem-comm-push-CS04-sw2-R c4) ▸ done

  b6 : Chain (Sw12 ∷ K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw23 ∷ []) (K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw12 ∷ CS04 ∷ K0 ∷ ι ∷ [])
  b6 = at 7 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 9 2 [] (wl0003 c4) ▸
       at 0 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 1 2 (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸
       at 2 2 (CX03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸
       at 3 2 (CS34⁻ ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS • CS • CS)) ▸
       at 4 2 (CX03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸ done

  b7 : Chain (K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw12 ∷ CS04 ∷ K0 ∷ ι ∷ []) (Sw23 ∷ K0 ∷ CS24 ∷ CX02 ∷ Sw23 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ [])
  b7 = at 5 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R c4) ▸
       at 6 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 7 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 2 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0011 c4)) ▸
       at 4 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0003 c4) ▸ done

  b8 : Chain (Sw23 ∷ K0 ∷ CS24 ∷ CX02 ∷ Sw23 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ K0 ∷ Sw12 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw12 ∷ [])
  b8 = at 4 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0012 c4)) ▸
       at 6 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0003 c4) ▸
       at 6 2 (CS04 ∷ Sw23 ∷ []) (lem-comm-push-CS04-sw2-R c4) ▸
       at 7 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 2 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸ done

  b9 : Chain (Sw23 ∷ Sw12 ∷ K0 ∷ Sw12 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ Sw12 ∷ ι ∷ Sw23 ∷ Sw12 ∷ [])
  b9 = at 3 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 c4)) ▸
       at 5 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0006 c4) ▸
       at 5 2 (CS14⁻ ∷ Sw12 ∷ []) (sym (wl0014 c4)) ▸
       at 7 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0006 c4) ▸
       at 7 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R c4) ▸
       at 8 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸ done

  b10 : Chain (Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ Sw12 ∷ ι ∷ Sw23 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw34 ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ [])
  b10 = at 9 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 5 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0004 c4) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0004 c4) ▸ done

  b11 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw34 ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ [])
  b11 = at 7 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 9 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0004 c4) ▸
       at 9 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 10 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b12 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ Sw23 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ [])
  b12 = at 5 2 [] (wl0003 c4) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0003 c4) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (wl0003 c4) ▸
       at 10 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸ done

  b13 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ Sw23 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Toff034 ∷ Sw12 ∷ [])
  b13 = at 11 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 4 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff014 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff024 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff034 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm push BOX(0;41) sw1 R: 3 steps
lem-comm-push-BOX⟨0·41⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Bx0-41 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-42 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·41⟩-sw1-R c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-41 ∷ []) (Bx0-42 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ14 ∷ []) (refl) ▸
       at 0 2 (CZ24 ∷ Sw12 ∷ []) (sym (wl0053 c4)) ▸
       at 0 1 (Bx0-42 ∷ []) (refl) ▸ done


-- comm push BOX(4;021) sw1 R: 12 steps
lem-comm-push-BOX⟨4·021⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Bx4-021 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-012 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨4·021⟩-sw1-R c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw12 ∷ Bx4-021 ∷ []) (CCZ014 ∷ Toff401 ∷ Bx0-42 ∷ Toff401 ∷ Sw12 ∷ CCZ024 ∷ Bx0-41 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff402 ∷ Bx0-41 ∷ Toff402 ∷ CCZ024 ∷ Bx0-41 ∷ []) (refl) ▸
       at 1 1 (Sw12 ∷ CCZ014 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0006 c4) ▸
       at 2 1 (Sw12 ∷ Toff401 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0006 c4) ▸
       at 2 2 (Bx0-42 ∷ Sw12 ∷ []) (lem-comm-push-BOX⟨0·41⟩-sw1-R c4) ▸
       at 4 1 (Sw12 ∷ Toff401 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0006 c4) ▸ done

  b1 : Chain (CCZ014 ∷ Toff401 ∷ Bx0-42 ∷ Toff401 ∷ Sw12 ∷ CCZ024 ∷ Bx0-41 ∷ []) (Bx4-012 ∷ Sw12 ∷ [])
  b1 = at 5 1 (Sw12 ∷ CCZ014 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0006 c4) ▸
       at 5 2 (Bx0-42 ∷ Sw12 ∷ []) (lem-comm-push-BOX⟨0·41⟩-sw1-R c4) ▸
       at 0 6 (Bx4-012 ∷ []) (refl) ▸ done


-- comm push BOX(0;4321) sw1 R: 8 steps
lem-comm-push-BOX⟨0·4321⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Bx0-4321 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4312 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·4321⟩-sw1-R c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-4321 ∷ []) (Bx0-4312 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff034 ∷ Bx4-021 ∷ Toff034 ∷ CCZ034 ∷ Bx4-021 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw12 ∷ []) (lem-comm-push-CCZ034-sw1-R c4) ▸
       at 1 2 (Toff034 ∷ Sw12 ∷ []) (lem-comm-push-TOFF034-sw1-R c4) ▸
       at 2 2 (Bx4-012 ∷ Sw12 ∷ []) (lem-comm-push-BOX⟨4·021⟩-sw1-R c4) ▸
       at 3 2 (Toff034 ∷ Sw12 ∷ []) (lem-comm-push-TOFF034-sw1-R c4) ▸
       at 4 2 (CCZ034 ∷ Sw12 ∷ []) (lem-comm-push-CCZ034-sw1-R c4) ▸
       at 5 2 (Bx4-012 ∷ Sw12 ∷ []) (lem-comm-push-BOX⟨4·021⟩-sw1-R c4) ▸
       at 0 6 (Bx0-4312 ∷ []) (refl) ▸ done


-- comm push SBOX(0;4;1;2) sw1 R: 3 steps
lem-comm-push-SBOX⟨0·4·1·2⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Sb0-4-1-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-4-2-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨0·4·1·2⟩-sw1-R c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb0-4-1-2 ∷ []) (Sb0-4-2-1 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS14 ∷ []) (refl) ▸
       at 0 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0005 c4)) ▸
       at 0 1 (Sb0-4-2-1 ∷ []) (refl) ▸ done


-- comm push SBOXd(0;4;1;2) sw1 R: 3 steps
lem-comm-push-SBOXd⟨0·4·1·2⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Sb⁻0-4-1-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-4-2-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨0·4·1·2⟩-sw1-R c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻0-4-1-2 ∷ []) (Sb⁻0-4-2-1 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS14⁻ ∷ []) (refl) ▸
       at 0 2 (CS24⁻ ∷ Sw12 ∷ []) (sym (wl0007 c4)) ▸
       at 0 1 (Sb⁻0-4-2-1 ∷ []) (refl) ▸ done


-- comm push SBOX(0;4;32;1) sw1 R: 7 steps
lem-comm-push-SBOX⟨0·4·32·1⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Sb0-4-32-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-4-31-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨0·4·32·1⟩-sw1-R c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb0-4-32-1 ∷ []) (Sb0-4-31-2 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx0-4321 ∷ Toff123 ∷ Sb0-4-1-2 ∷ Toff123 ∷ Sb⁻0-4-1-2 ∷ []) (refl) ▸
       at 0 2 (Bx0-4312 ∷ Sw12 ∷ []) (lem-comm-push-BOX⟨0·4321⟩-sw1-R c4) ▸
       at 1 2 (Toff213 ∷ Sw12 ∷ []) (wl0127 c4) ▸
       at 2 2 (Sb0-4-2-1 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·4·1·2⟩-sw1-R c4) ▸
       at 3 2 (Toff213 ∷ Sw12 ∷ []) (wl0127 c4) ▸
       at 4 2 (Sb⁻0-4-2-1 ∷ Sw12 ∷ []) (lem-comm-push-SBOXd⟨0·4·1·2⟩-sw1-R c4) ▸
       at 0 5 (Sb0-4-31-2 ∷ []) (refl) ▸ done


-- comm push TOFF401 sw2 R: 62 steps
lem-comm-push-TOFF401-sw2-R : WsL → ⟪ (Sw23 ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-TOFF401-sw2-R c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (Sw23 ∷ Toff401 ∷ []) (Sw23 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Toff301 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (K3 ∷ Sw23 ∷ []) (sym (wl0064 c4)) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸ done

  b1 : Chain (Sw23 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ K4 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ [])
  b1 = at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K3 ∷ Sw23 ∷ []) (sym (wl0064 c4)) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 10 2 [] (wl0003 c4) ▸
       at 1 2 (K4 ∷ Sw34 ∷ []) (sym (wl0065 c4)) ▸ done

  b2 : Chain (Sw23 ∷ K4 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ []) (Sw23 ∷ K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw34 ∷ K3 ∷ ι ∷ Sw34 ∷ [])
  b2 = at 4 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 4 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (Sw23 ∷ K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw34 ∷ K3 ∷ ι ∷ Sw34 ∷ []) (K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw23 ∷ CS04 ∷ K4 ∷ ι ∷ [])
  b3 = at 7 2 (K4 ∷ Sw34 ∷ []) (sym (wl0065 c4)) ▸
       at 8 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 9 2 [] (wl0004 c4) ▸
       at 0 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸
       at 1 2 (CS14 ∷ Sw23 ∷ []) (sym (wl0017 c4)) ▸
       at 2 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 3 2 (CS14⁻ ∷ Sw23 ∷ []) (sym (wl0048 c4)) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸ done

  b4 : Chain (K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw23 ∷ CS04 ∷ K4 ∷ ι ∷ []) (Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ Sw34 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K4 ∷ ι ∷ Sw23 ∷ [])
  b4 = at 5 2 (CS04 ∷ Sw23 ∷ []) (lem-comm-push-CS04-sw2-R c4) ▸
       at 6 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸
       at 7 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 2 (K3 ∷ Sw34 ∷ []) (sym (wl0066 c4)) ▸
       at 3 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0004 c4) ▸
       at 3 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸ done

  b5 : Chain (Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ Sw34 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K4 ∷ ι ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw23 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw23 ∷ [])
  b5 = at 5 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0004 c4) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0004 c4) ▸
       at 7 2 (K3 ∷ Sw34 ∷ []) (sym (wl0066 c4)) ▸
       at 8 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸ done

  b6 : Chain (Sw34 ∷ Sw23 ∷ Sw23 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw23 ∷ [])
  b6 = at 2 2 (K2 ∷ Sw23 ∷ []) (sym (wl0067 c4)) ▸
       at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0003 c4) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0003 c4) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b7 : Chain (Sw34 ∷ Sw23 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw23 ∷ []) (Toff401 ∷ Sw23 ∷ [])
  b7 = at 7 2 [] (wl0003 c4) ▸
       at 8 2 (K2 ∷ Sw23 ∷ []) (sym (wl0067 c4)) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 2 8 (Toff201 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff301 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff401 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm push BOX(0;42) sw2 R: 3 steps
lem-comm-push-BOX⟨0·42⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Bx0-42 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-43 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·42⟩-sw2-R c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-42 ∷ []) (Bx0-43 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ24 ∷ []) (refl) ▸
       at 0 2 (CZ34 ∷ Sw23 ∷ []) (sym (wl0035 c4)) ▸
       at 0 1 (Bx0-43 ∷ []) (refl) ▸ done


-- comm push BOX(4;012) sw2 R: 8 steps
lem-comm-push-BOX⟨4·012⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Bx4-012 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-013 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨4·012⟩-sw2-R c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-012 ∷ []) (Bx4-013 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff401 ∷ Bx0-42 ∷ Toff401 ∷ CCZ014 ∷ Bx0-42 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw23 ∷ []) (lem-comm-push-CCZ014-sw2-R c4) ▸
       at 1 2 (Toff401 ∷ Sw23 ∷ []) (lem-comm-push-TOFF401-sw2-R c4) ▸
       at 2 2 (Bx0-43 ∷ Sw23 ∷ []) (lem-comm-push-BOX⟨0·42⟩-sw2-R c4) ▸
       at 3 2 (Toff401 ∷ Sw23 ∷ []) (lem-comm-push-TOFF401-sw2-R c4) ▸
       at 4 2 (CCZ014 ∷ Sw23 ∷ []) (lem-comm-push-CCZ014-sw2-R c4) ▸
       at 5 2 (Bx0-43 ∷ Sw23 ∷ []) (lem-comm-push-BOX⟨0·42⟩-sw2-R c4) ▸
       at 0 6 (Bx4-013 ∷ []) (refl) ▸ done


-- comm push BOX(0;4312) sw2 R: 12 steps
lem-comm-push-BOX⟨0·4312⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Bx0-4312 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4213 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·4312⟩-sw2-R c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw23 ∷ Bx0-4312 ∷ []) (CCZ024 ∷ Toff024 ∷ Bx4-013 ∷ Toff024 ∷ Sw23 ∷ CCZ034 ∷ Bx4-012 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff034 ∷ Bx4-012 ∷ Toff034 ∷ CCZ034 ∷ Bx4-012 ∷ []) (refl) ▸
       at 1 1 (Sw23 ∷ CCZ024 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0003 c4) ▸
       at 2 1 (Sw23 ∷ Toff024 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0003 c4) ▸
       at 2 2 (Bx4-013 ∷ Sw23 ∷ []) (lem-comm-push-BOX⟨4·012⟩-sw2-R c4) ▸
       at 4 1 (Sw23 ∷ Toff024 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0003 c4) ▸ done

  b1 : Chain (CCZ024 ∷ Toff024 ∷ Bx4-013 ∷ Toff024 ∷ Sw23 ∷ CCZ034 ∷ Bx4-012 ∷ []) (Bx0-4213 ∷ Sw23 ∷ [])
  b1 = at 5 1 (Sw23 ∷ CCZ024 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0003 c4) ▸
       at 5 2 (Bx4-013 ∷ Sw23 ∷ []) (lem-comm-push-BOX⟨4·012⟩-sw2-R c4) ▸
       at 0 6 (Bx0-4213 ∷ []) (refl) ▸ done


-- comm push SBOX(0;4;2;1) sw2 R: 3 steps
lem-comm-push-SBOX⟨0·4·2·1⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Sb0-4-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-4-3-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨0·4·2·1⟩-sw2-R c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb0-4-2-1 ∷ []) (Sb0-4-3-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS24 ∷ []) (refl) ▸
       at 0 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0008 c4)) ▸
       at 0 1 (Sb0-4-3-1 ∷ []) (refl) ▸ done


-- comm push SBOXd(0;4;2;1) sw2 R: 3 steps
lem-comm-push-SBOXd⟨0·4·2·1⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Sb⁻0-4-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-4-3-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨0·4·2·1⟩-sw2-R c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻0-4-2-1 ∷ []) (Sb⁻0-4-3-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS24⁻ ∷ []) (refl) ▸
       at 0 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0009 c4)) ▸
       at 0 1 (Sb⁻0-4-3-1 ∷ []) (refl) ▸ done


-- comm push SBOX(0;4;31;2) sw2 R: 7 steps
lem-comm-push-SBOX⟨0·4·31·2⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Sb0-4-31-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-4-21-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨0·4·31·2⟩-sw2-R c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb0-4-31-2 ∷ []) (Sb0-4-21-3 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx0-4312 ∷ Toff213 ∷ Sb0-4-2-1 ∷ Toff213 ∷ Sb⁻0-4-2-1 ∷ []) (refl) ▸
       at 0 2 (Bx0-4213 ∷ Sw23 ∷ []) (lem-comm-push-BOX⟨0·4312⟩-sw2-R c4) ▸
       at 1 2 (Toff312 ∷ Sw23 ∷ []) (wl0126 c4) ▸
       at 2 2 (Sb0-4-3-1 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·4·2·1⟩-sw2-R c4) ▸
       at 3 2 (Toff312 ∷ Sw23 ∷ []) (wl0126 c4) ▸
       at 4 2 (Sb⁻0-4-3-1 ∷ Sw23 ∷ []) (lem-comm-push-SBOXd⟨0·4·2·1⟩-sw2-R c4) ▸
       at 0 5 (Sb0-4-21-3 ∷ []) (refl) ▸ done


-- comm push CCZ024 sw0 R: 46 steps
lem-comm-push-CCZ024-sw0-R : WsL → ⟪ (Sw01 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-CCZ024-sw0-R c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (run b5)))))
  where
  b0 : Chain (Sw01 ∷ CCZ024 ∷ []) (Sw01 ∷ Sw12 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw12 ∷ CCZ014 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ CCZ013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸ done

  b1 : Chain (Sw01 ∷ Sw12 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) (Sw01 ∷ Sw12 ∷ CS14 ∷ CX01 ∷ Sw34 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ [])
  b1 = at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0003 c4) ▸
       at 4 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸ done

  b2 : Chain (Sw01 ∷ Sw12 ∷ CS14 ∷ CX01 ∷ Sw34 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ []) (Sw01 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw12 ∷ [])
  b2 = at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 4 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0004 c4) ▸
       at 1 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0005 c4)) ▸
       at 4 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸ done

  b3 : Chain (Sw01 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw12 ∷ []) (CS24 ∷ CX12 ∷ Sw01 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ [])
  b3 = at 2 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS24⁻ ∷ Sw12 ∷ []) (sym (wl0007 c4)) ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R c4) ▸
       at 6 2 [] (wl0006 c4) ▸
       at 0 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 1 2 (CX12 ∷ Sw01 ∷ []) (sym (wl0117 c4)) ▸ done

  b4 : Chain (CS24 ∷ CX12 ∷ Sw01 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ []) (Sw34 ∷ CS23 ∷ CX12 ∷ Sw34 ∷ Sw34 ∷ CS23⁻ ∷ Sw34 ∷ CX12 ∷ CS14 ∷ Sw01 ∷ [])
  b4 = at 2 2 (CS24⁻ ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • (CS • CS • CS) • Swap ↑)) ▸
       at 3 2 (CX12 ∷ Sw01 ∷ []) (sym (wl0117 c4)) ▸
       at 4 2 (CS14 ∷ Sw01 ∷ []) (lem-comm-push-CS04-sw0-R c4) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0004 c4) ▸
       at 2 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 4 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b5 : Chain (Sw34 ∷ CS23 ∷ CX12 ∷ Sw34 ∷ Sw34 ∷ CS23⁻ ∷ Sw34 ∷ CX12 ∷ CS14 ∷ Sw01 ∷ []) (CCZ124 ∷ Sw01 ∷ [])
  b5 = at 3 2 [] (wl0004 c4) ▸
       at 4 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 6 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0004 c4) ▸
       at 1 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (CCZ124 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm push TOFF024 sw0 R: 62 steps
lem-comm-push-TOFF024-sw0-R : WsL → ⟪ (Sw01 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff124 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-TOFF024-sw0-R c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (Sw01 ∷ Toff024 ∷ []) (Sw01 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Toff014 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸ done

  b1 : Chain (Sw01 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) (Sw01 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ [])
  b1 = at 8 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 10 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 11 2 [] (wl0003 c4) ▸ done

  b2 : Chain (Sw01 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ []) (Sw01 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ [])
  b2 = at 2 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 5 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 9 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸ done

  b3 : Chain (Sw01 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ []) (Sw01 ∷ K0 ∷ CS24 ∷ CX02 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ [])
  b3 = at 7 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 9 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 10 2 [] (wl0004 c4) ▸
       at 1 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 2 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0005 c4)) ▸
       at 5 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 3 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (Sw01 ∷ K0 ∷ CS24 ∷ CX02 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ []) (K1 ∷ Sw01 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0 ∷ ι ∷ [])
  b4 = at 4 2 (CS24⁻ ∷ Sw12 ∷ []) (sym (wl0007 c4)) ▸
       at 7 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 5 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R c4) ▸
       at 7 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 8 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 9 2 [] (wl0006 c4) ▸
       at 0 2 (K1 ∷ Sw01 ∷ []) (sym (wl0109 c4)) ▸ done

  b5 : Chain (K1 ∷ Sw01 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0 ∷ ι ∷ []) (Sw34 ∷ Sw34 ∷ K1 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K1 ∷ ι ∷ Sw01 ∷ [])
  b5 = at 1 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 2 2 (CX12 ∷ Sw01 ∷ []) (sym (wl0117 c4)) ▸
       at 3 2 (CS24⁻ ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • (CS • CS • CS) • Swap ↑)) ▸
       at 4 2 (CX12 ∷ Sw01 ∷ []) (sym (wl0117 c4)) ▸
       at 5 2 (CS14 ∷ Sw01 ∷ []) (lem-comm-push-CS04-sw0-R c4) ▸
       at 6 2 (K1 ∷ Sw01 ∷ []) (sym (wl0109 c4)) ▸
       at 7 2 (ι ∷ Sw01 ∷ []) (wl0025 c4) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸ done

  b6 : Chain (Sw34 ∷ Sw34 ∷ K1 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K1 ∷ ι ∷ Sw01 ∷ []) (Sw34 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw34 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ K1 ∷ ι ∷ Sw01 ∷ [])
  b6 = at 1 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 3 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0004 c4) ▸
       at 3 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 5 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0004 c4) ▸
       at 5 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 7 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b7 : Chain (Sw34 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw34 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ K1 ∷ ι ∷ Sw01 ∷ []) (Toff124 ∷ Sw01 ∷ [])
  b7 = at 6 2 [] (wl0004 c4) ▸
       at 7 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 8 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 1 8 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (wl0027 c4) ▸
       at 1 8 (Toff123 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff124 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm push TOFF401 sw0 R: 63 steps
lem-comm-push-TOFF401-sw0-R : WsL → ⟪ (Sw01 ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-TOFF401-sw0-R c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (Sw01 ∷ Toff401 ∷ []) (Sw01 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Toff301 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (K3 ∷ Sw23 ∷ []) (sym (wl0064 c4)) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸ done

  b1 : Chain (Sw01 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw34 ∷ []) (Sw01 ∷ K4 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ [])
  b1 = at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K3 ∷ Sw23 ∷ []) (sym (wl0064 c4)) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 10 2 [] (wl0003 c4) ▸
       at 1 2 (K4 ∷ Sw34 ∷ []) (sym (wl0065 c4)) ▸ done

  b2 : Chain (Sw01 ∷ K4 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ []) (Sw01 ∷ K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw34 ∷ K3 ∷ ι ∷ Sw34 ∷ [])
  b2 = at 4 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 4 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (Sw01 ∷ K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw34 ∷ K3 ∷ ι ∷ Sw34 ∷ []) (K4 ∷ CS04 ∷ CX10 ∷ CS04⁻ ∷ CX10 ∷ Sw01 ∷ CS04 ∷ K4 ∷ ι ∷ [])
  b3 = at 7 2 (K4 ∷ Sw34 ∷ []) (sym (wl0065 c4)) ▸
       at 8 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 9 2 [] (wl0004 c4) ▸
       at 0 2 (K4 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ ↑)) ▸
       at 1 2 (CS04 ∷ Sw01 ∷ []) (lem-comm-push-CS14-sw0-R c4) ▸
       at 2 2 (CX10 ∷ Sw01 ∷ []) (sym (wl0115 c4)) ▸
       at 3 2 (CS04⁻ ∷ Sw01 ∷ []) (lem-comm-push-CSd14-sw0-R c4) ▸
       at 4 2 (CX10 ∷ Sw01 ∷ []) (sym (wl0115 c4)) ▸ done

  b4 : Chain (K4 ∷ CS04 ∷ CX10 ∷ CS04⁻ ∷ CX10 ∷ Sw01 ∷ CS04 ∷ K4 ∷ ι ∷ []) (Sw34 ∷ K3 ∷ CS03 ∷ CX10 ∷ Sw34 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ K4 ∷ ι ∷ Sw01 ∷ [])
  b4 = at 5 2 (CS14 ∷ Sw01 ∷ []) (lem-comm-push-CS04-sw0-R c4) ▸
       at 6 2 (K4 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ ↑)) ▸
       at 7 2 (ι ∷ Sw01 ∷ []) (wl0025 c4) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 2 (K3 ∷ Sw34 ∷ []) (sym (wl0066 c4)) ▸
       at 3 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0004 c4) ▸
       at 3 2 (CX10 ∷ Sw34 ∷ []) (sym (c₂ (CX₁₀) (Swap ↑))) ▸ done

  b5 : Chain (Sw34 ∷ K3 ∷ CS03 ∷ CX10 ∷ Sw34 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ K4 ∷ ι ∷ Sw01 ∷ []) (Sw34 ∷ Sw23 ∷ Sw23 ∷ K3 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw01 ∷ [])
  b5 = at 5 1 (Sw34 ∷ CS03⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0004 c4) ▸
       at 5 2 (CX10 ∷ Sw34 ∷ []) (sym (c₂ (CX₁₀) (Swap ↑))) ▸
       at 7 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0004 c4) ▸
       at 7 2 (K3 ∷ Sw34 ∷ []) (sym (wl0066 c4)) ▸
       at 8 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸ done

  b6 : Chain (Sw34 ∷ Sw23 ∷ Sw23 ∷ K3 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw01 ∷ []) (Sw34 ∷ Sw23 ∷ K2 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw01 ∷ [])
  b6 = at 2 2 (K2 ∷ Sw23 ∷ []) (sym (wl0067 c4)) ▸
       at 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0003 c4) ▸
       at 4 2 (CX10 ∷ Sw23 ∷ []) (sym (c₂ (CX₁₀) (Swap))) ▸
       at 6 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0003 c4) ▸
       at 6 2 (CX10 ∷ Sw23 ∷ []) (sym (c₂ (CX₁₀) (Swap))) ▸
       at 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b7 : Chain (Sw34 ∷ Sw23 ∷ K2 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw01 ∷ []) (Toff401 ∷ Sw01 ∷ [])
  b7 = at 7 2 [] (wl0003 c4) ▸
       at 8 2 (K2 ∷ Sw23 ∷ []) (sym (wl0067 c4)) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 2 8 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (wl0124 c4) ▸
       at 2 8 (Toff201 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff301 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff401 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm push BOX(4;013) sw0 R: 8 steps
lem-comm-push-BOX⟨4·013⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Bx4-013 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-103 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨4·013⟩-sw0-R c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-013 ∷ []) (Bx4-103 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff401 ∷ Bx0-43 ∷ Toff401 ∷ CCZ014 ∷ Bx0-43 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw01 ∷ []) (lem-comm-push-CCZ014-sw0-R c4) ▸
       at 1 2 (Toff401 ∷ Sw01 ∷ []) (lem-comm-push-TOFF401-sw0-R c4) ▸
       at 2 2 (Bx0-43 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸
       at 3 2 (Toff401 ∷ Sw01 ∷ []) (lem-comm-push-TOFF401-sw0-R c4) ▸
       at 4 2 (CCZ014 ∷ Sw01 ∷ []) (lem-comm-push-CCZ014-sw0-R c4) ▸
       at 5 2 (Bx0-43 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸
       at 0 6 (Bx4-103 ∷ []) (refl) ▸ done


-- comm push BOX(0;4213) sw0 R: 8 steps
lem-comm-push-BOX⟨0·4213⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Bx0-4213 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-4203 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·4213⟩-sw0-R c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-4213 ∷ []) (Bx1-4203 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx4-013 ∷ Toff024 ∷ CCZ024 ∷ Bx4-013 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw01 ∷ []) (lem-comm-push-CCZ024-sw0-R c4) ▸
       at 1 2 (Toff124 ∷ Sw01 ∷ []) (lem-comm-push-TOFF024-sw0-R c4) ▸
       at 2 2 (Bx4-103 ∷ Sw01 ∷ []) (lem-comm-push-BOX⟨4·013⟩-sw0-R c4) ▸
       at 3 2 (Toff124 ∷ Sw01 ∷ []) (lem-comm-push-TOFF024-sw0-R c4) ▸
       at 4 2 (CCZ124 ∷ Sw01 ∷ []) (lem-comm-push-CCZ024-sw0-R c4) ▸
       at 5 2 (Bx4-103 ∷ Sw01 ∷ []) (lem-comm-push-BOX⟨4·013⟩-sw0-R c4) ▸
       at 0 6 (Bx1-4203 ∷ []) (refl) ▸ done


-- comm push SBOX(0;4;21;3) sw0 R: 7 steps
lem-comm-push-SBOX⟨0·4·21·3⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Sb0-4-21-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-4-20-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨0·4·21·3⟩-sw0-R c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb0-4-21-3 ∷ []) (Sb1-4-20-3 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx0-4213 ∷ Toff312 ∷ Sb0-4-3-1 ∷ Toff312 ∷ Sb⁻0-4-3-1 ∷ []) (refl) ▸
       at 0 2 (Bx1-4203 ∷ Sw01 ∷ []) (lem-comm-push-BOX⟨0·4213⟩-sw0-R c4) ▸
       at 1 2 (Toff302 ∷ Sw01 ∷ []) (wl0063 c4) ▸
       at 2 2 (Sb0-4-3-1 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑)) ▸
       at 3 2 (Toff302 ∷ Sw01 ∷ []) (wl0063 c4) ▸
       at 4 2 (Sb⁻0-4-3-1 ∷ Sw01 ∷ []) (c₂ (Swap) ((CS • CS • CS) ↑)) ▸
       at 0 5 (Sb1-4-20-3 ∷ []) (refl) ▸ done


-- comm push BOX(4;103) sw1 R: 12 steps
lem-comm-push-BOX⟨4·103⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Bx4-103 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-203 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨4·103⟩-sw1-R c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw12 ∷ Bx4-103 ∷ []) (CCZ024 ∷ Toff402 ∷ Bx1-43 ∷ Toff402 ∷ Sw12 ∷ CCZ014 ∷ Bx1-43 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff401 ∷ Bx1-43 ∷ Toff401 ∷ CCZ014 ∷ Bx1-43 ∷ []) (refl) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 0 3 (CCZ024 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 1 3 (Toff402 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Bx1-43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ)) ▸
       at 5 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 3 3 (Toff402 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff402 ∷ Bx1-43 ∷ Toff402 ∷ Sw12 ∷ CCZ014 ∷ Bx1-43 ∷ []) (Bx4-203 ∷ Sw12 ∷ [])
  b1 = at 6 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 4 3 (CCZ024 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Bx1-43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ)) ▸
       at 0 6 (Bx4-203 ∷ []) (refl) ▸ done


-- comm push BOX(1;4203) sw1 R: 8 steps
lem-comm-push-BOX⟨1·4203⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Bx1-4203 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4103 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨1·4203⟩-sw1-R c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-4203 ∷ []) (Bx2-4103 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff124 ∷ Bx4-103 ∷ Toff124 ∷ CCZ124 ∷ Bx4-103 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0122 c4)) ▸
       at 1 2 (Toff214 ∷ Sw12 ∷ []) (wl0123 c4) ▸
       at 2 2 (Bx4-203 ∷ Sw12 ∷ []) (lem-comm-push-BOX⟨4·103⟩-sw1-R c4) ▸
       at 3 2 (Toff214 ∷ Sw12 ∷ []) (wl0123 c4) ▸
       at 4 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0122 c4)) ▸
       at 5 2 (Bx4-203 ∷ Sw12 ∷ []) (lem-comm-push-BOX⟨4·103⟩-sw1-R c4) ▸
       at 0 6 (Bx2-4103 ∷ []) (refl) ▸ done


-- comm push SBOX(1;4;20;3) sw1 R: 9 steps
lem-comm-push-SBOX⟨1·4·20·3⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Sb1-4-20-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-10-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨1·4·20·3⟩-sw1-R c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw12 ∷ Sb1-4-20-3 ∷ []) (Bx2-4103 ∷ Toff301 ∷ Sb1-4-3-0 ∷ Toff301 ∷ Sb⁻1-4-3-0 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx1-4203 ∷ Toff302 ∷ Sb1-4-3-0 ∷ Toff302 ∷ Sb⁻1-4-3-0 ∷ []) (refl) ▸
       at 0 2 (Bx2-4103 ∷ Sw12 ∷ []) (lem-comm-push-BOX⟨1·4203⟩-sw1-R c4) ▸
       at 2 1 (Sw12 ∷ Toff301 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0006 c4) ▸
       at 2 2 (Sb1-4-3-0 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸
       at 4 1 (Sw12 ∷ Toff301 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0006 c4) ▸
       at 4 2 (Sb⁻1-4-3-0 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS • CS • CS)) ▸ done

  b1 : Chain (Bx2-4103 ∷ Toff301 ∷ Sb1-4-3-0 ∷ Toff301 ∷ Sb⁻1-4-3-0 ∷ Sw12 ∷ []) (Sb2-4-10-3 ∷ Sw12 ∷ [])
  b1 = at 0 5 (Sb2-4-10-3 ∷ []) (refl) ▸ done


-- comm push CCZ124 sw0 R: 46 steps
lem-comm-push-CCZ124-sw0-R : WsL → ⟪ (Sw01 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-CCZ124-sw0-R c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (run b5)))))
  where
  b0 : Chain (Sw01 ∷ CCZ124 ∷ []) (Sw01 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 3 (CS24 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸ done

  b1 : Chain (Sw01 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ []) (CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ Sw01 ∷ [])
  b1 = at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 5 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0004 c4) ▸
       at 0 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 1 2 (CX02 ∷ Sw01 ∷ []) (sym (wl0039 c4)) ▸
       at 2 2 (CS24⁻ ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • (CS • CS • CS) • Swap ↑)) ▸
       at 3 2 (CX02 ∷ Sw01 ∷ []) (sym (wl0039 c4)) ▸
       at 4 2 (CS04 ∷ Sw01 ∷ []) (lem-comm-push-CS14-sw0-R c4) ▸ done

  b2 : Chain (CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ Sw01 ∷ []) (Sw12 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ [])
  b2 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 1 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 c4)) ▸
       at 3 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0006 c4) ▸
       at 3 2 (CS14⁻ ∷ Sw12 ∷ []) (sym (wl0014 c4)) ▸
       at 5 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0006 c4) ▸
       at 5 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R c4) ▸ done

  b3 : Chain (Sw12 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ []) (Sw12 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw34 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ [])
  b3 = at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0004 c4) ▸
       at 3 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 5 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0004 c4) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (Sw12 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw34 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ []) (Sw12 ∷ Sw34 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ [])
  b4 = at 6 2 [] (wl0004 c4) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0003 c4) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0003 c4) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸ done

  b5 : Chain (Sw12 ∷ Sw34 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ []) (CCZ024 ∷ Sw01 ∷ [])
  b5 = at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0003 c4) ▸
       at 3 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (CCZ014 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (CCZ024 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm push TOFF214 sw0 R: 62 steps
lem-comm-push-TOFF214-sw0-R : WsL → ⟪ (Sw01 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-TOFF214-sw0-R c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (Sw01 ∷ Toff214 ∷ []) (Sw01 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Sw34 ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Toff213 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (K2 ∷ Sw34 ∷ []) (sym (c₃ (K ↑ ↑) (Swap))) ▸
       at 4 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 3 (CS24 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 4 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw01 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Sw34 ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ Sw34 ∷ []) (K2 ∷ CS24 ∷ Sw01 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2 ∷ ι1 ∷ [])
  b1 = at 5 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 6 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K2 ∷ Sw34 ∷ []) (sym (c₃ (K ↑ ↑) (Swap))) ▸
       at 8 2 (ι1 ∷ Sw34 ∷ []) (sym (c₂ (iI ↑) (Swap ↑))) ▸
       at 9 2 [] (wl0004 c4) ▸
       at 0 2 (K2 ∷ Sw01 ∷ []) (c₂ (Swap) (K)) ▸
       at 1 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸ done

  b2 : Chain (K2 ∷ CS24 ∷ Sw01 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2 ∷ ι1 ∷ []) (Sw12 ∷ K1 ∷ Sw12 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K2 ∷ ι1 ∷ Sw01 ∷ [])
  b2 = at 2 2 (CX02 ∷ Sw01 ∷ []) (sym (wl0039 c4)) ▸
       at 3 2 (CS24⁻ ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • (CS • CS • CS) • Swap ↑)) ▸
       at 4 2 (CX02 ∷ Sw01 ∷ []) (sym (wl0039 c4)) ▸
       at 5 2 (CS04 ∷ Sw01 ∷ []) (lem-comm-push-CS14-sw0-R c4) ▸
       at 6 2 (K2 ∷ Sw01 ∷ []) (c₂ (Swap) (K)) ▸
       at 7 2 (ι1 ∷ Sw01 ∷ []) (wl0118 c4) ▸
       at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 1 2 (K1 ∷ Sw12 ∷ []) (sym (wl0073 c4)) ▸ done

  b3 : Chain (Sw12 ∷ K1 ∷ Sw12 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K2 ∷ ι1 ∷ Sw01 ∷ []) (Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ Sw12 ∷ ι1 ∷ Sw01 ∷ [])
  b3 = at 2 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 c4)) ▸
       at 4 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0006 c4) ▸
       at 4 2 (CS14⁻ ∷ Sw12 ∷ []) (sym (wl0014 c4)) ▸
       at 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0006 c4) ▸
       at 6 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R c4) ▸
       at 7 2 (K1 ∷ Sw12 ∷ []) (sym (wl0073 c4)) ▸ done

  b4 : Chain (Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ Sw12 ∷ ι1 ∷ Sw01 ∷ []) (Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw34 ∷ CX01 ∷ CS04 ∷ K1 ∷ ι1 ∷ Sw12 ∷ Sw01 ∷ [])
  b4 = at 8 2 (ι1 ∷ Sw12 ∷ []) (wl0119 c4) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 4 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0004 c4) ▸
       at 4 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 6 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0004 c4) ▸ done

  b5 : Chain (Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw34 ∷ CX01 ∷ CS04 ∷ K1 ∷ ι1 ∷ Sw12 ∷ Sw01 ∷ []) (Sw12 ∷ Sw34 ∷ Sw23 ∷ K1 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι1 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ [])
  b5 = at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0004 c4) ▸
       at 8 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 9 2 (ι1 ∷ Sw34 ∷ []) (sym (c₂ (iI ↑) (Swap ↑))) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 3 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b6 : Chain (Sw12 ∷ Sw34 ∷ Sw23 ∷ K1 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι1 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ []) (Sw12 ∷ Sw34 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ Sw23 ∷ ι1 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ [])
  b6 = at 4 2 [] (wl0003 c4) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0003 c4) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0003 c4) ▸
       at 9 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸ done

  b7 : Chain (Sw12 ∷ Sw34 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ Sw23 ∷ ι1 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ []) (Toff204 ∷ Sw01 ∷ [])
  b7 = at 10 2 (ι1 ∷ Sw23 ∷ []) (sym (c₂ (iI ↑) (Swap))) ▸
       at 3 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (sym (wl0134 c4)) ▸
       at 3 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff103 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff104 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff204 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm push TOFF402 sw0 R: 62 steps
lem-comm-push-TOFF402-sw0-R : WsL → ⟪ (Sw01 ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-TOFF402-sw0-R c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (Sw01 ∷ Toff402 ∷ []) (Sw01 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Toff401 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Toff301 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (K3 ∷ Sw23 ∷ []) (sym (wl0064 c4)) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸ done

  b1 : Chain (Sw01 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) (Sw01 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw12 ∷ [])
  b1 = at 8 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K3 ∷ Sw23 ∷ []) (sym (wl0064 c4)) ▸
       at 10 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 11 2 [] (wl0003 c4) ▸ done

  b2 : Chain (Sw01 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw12 ∷ []) (Sw01 ∷ Sw12 ∷ K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw34 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw12 ∷ [])
  b2 = at 2 2 (K4 ∷ Sw34 ∷ []) (sym (wl0065 c4)) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 5 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 9 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸ done

  b3 : Chain (Sw01 ∷ Sw12 ∷ K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw34 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw12 ∷ []) (Sw01 ∷ K4 ∷ CS24 ∷ CX02 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K4 ∷ ι ∷ Sw12 ∷ [])
  b3 = at 7 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K4 ∷ Sw34 ∷ []) (sym (wl0065 c4)) ▸
       at 9 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 10 2 [] (wl0004 c4) ▸
       at 1 2 (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑)) ▸
       at 2 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0005 c4)) ▸
       at 5 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 3 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (Sw01 ∷ K4 ∷ CS24 ∷ CX02 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K4 ∷ ι ∷ Sw12 ∷ []) (K4 ∷ Sw01 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K4 ∷ ι ∷ [])
  b4 = at 4 2 (CS24⁻ ∷ Sw12 ∷ []) (sym (wl0007 c4)) ▸
       at 7 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 5 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R c4) ▸
       at 7 2 (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑)) ▸
       at 8 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 9 2 [] (wl0006 c4) ▸
       at 0 2 (K4 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ ↑)) ▸ done

  b5 : Chain (K4 ∷ Sw01 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K4 ∷ ι ∷ []) (Sw34 ∷ Sw34 ∷ K4 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K4 ∷ ι ∷ Sw01 ∷ [])
  b5 = at 1 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 2 2 (CX12 ∷ Sw01 ∷ []) (sym (wl0117 c4)) ▸
       at 3 2 (CS24⁻ ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • (CS • CS • CS) • Swap ↑)) ▸
       at 4 2 (CX12 ∷ Sw01 ∷ []) (sym (wl0117 c4)) ▸
       at 5 2 (CS14 ∷ Sw01 ∷ []) (lem-comm-push-CS04-sw0-R c4) ▸
       at 6 2 (K4 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ ↑)) ▸
       at 7 2 (ι ∷ Sw01 ∷ []) (wl0025 c4) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸ done

  b6 : Chain (Sw34 ∷ Sw34 ∷ K4 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K4 ∷ ι ∷ Sw01 ∷ []) (Sw34 ∷ K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw34 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ K4 ∷ ι ∷ Sw01 ∷ [])
  b6 = at 1 2 (K3 ∷ Sw34 ∷ []) (sym (wl0066 c4)) ▸
       at 3 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0004 c4) ▸
       at 3 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 5 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0004 c4) ▸
       at 5 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 7 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b7 : Chain (Sw34 ∷ K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw34 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ K4 ∷ ι ∷ Sw01 ∷ []) (Toff412 ∷ Sw01 ∷ [])
  b7 = at 6 2 [] (wl0004 c4) ▸
       at 7 2 (K3 ∷ Sw34 ∷ []) (sym (wl0066 c4)) ▸
       at 8 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 1 8 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) (wl0068 c4) ▸
       at 1 8 (Toff312 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff412 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm push BOX(4;203) sw0 R: 8 steps
lem-comm-push-BOX⟨4·203⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Bx4-203 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-213 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨4·203⟩-sw0-R c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-203 ∷ []) (Bx4-213 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff402 ∷ Bx2-43 ∷ Toff402 ∷ CCZ024 ∷ Bx2-43 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw01 ∷ []) (lem-comm-push-CCZ024-sw0-R c4) ▸
       at 1 2 (Toff412 ∷ Sw01 ∷ []) (lem-comm-push-TOFF402-sw0-R c4) ▸
       at 2 2 (Bx2-43 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸
       at 3 2 (Toff412 ∷ Sw01 ∷ []) (lem-comm-push-TOFF402-sw0-R c4) ▸
       at 4 2 (CCZ124 ∷ Sw01 ∷ []) (lem-comm-push-CCZ024-sw0-R c4) ▸
       at 5 2 (Bx2-43 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸
       at 0 6 (Bx4-213 ∷ []) (refl) ▸ done


-- comm push BOX(2;4103) sw0 R: 8 steps
lem-comm-push-BOX⟨2·4103⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Bx2-4103 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨2·4103⟩-sw0-R c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-4103 ∷ []) (Bx2-4013 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff214 ∷ Bx4-203 ∷ Toff214 ∷ CCZ124 ∷ Bx4-203 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw01 ∷ []) (lem-comm-push-CCZ124-sw0-R c4) ▸
       at 1 2 (Toff204 ∷ Sw01 ∷ []) (lem-comm-push-TOFF214-sw0-R c4) ▸
       at 2 2 (Bx4-213 ∷ Sw01 ∷ []) (lem-comm-push-BOX⟨4·203⟩-sw0-R c4) ▸
       at 3 2 (Toff204 ∷ Sw01 ∷ []) (lem-comm-push-TOFF214-sw0-R c4) ▸
       at 4 2 (CCZ024 ∷ Sw01 ∷ []) (lem-comm-push-CCZ124-sw0-R c4) ▸
       at 5 2 (Bx4-213 ∷ Sw01 ∷ []) (lem-comm-push-BOX⟨4·203⟩-sw0-R c4) ▸
       at 0 6 (Bx2-4013 ∷ []) (refl) ▸ done


-- comm push SBOX(2;4;10;3) sw0 R: 7 steps
lem-comm-push-SBOX⟨2·4·10·3⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Sb2-4-10-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-01-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨2·4·10·3⟩-sw0-R c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb2-4-10-3 ∷ []) (Sb2-4-01-3 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx2-4103 ∷ Toff301 ∷ Sb2-4-3-0 ∷ Toff301 ∷ Sb⁻2-4-3-0 ∷ []) (refl) ▸
       at 0 2 (Bx2-4013 ∷ Sw01 ∷ []) (lem-comm-push-BOX⟨2·4103⟩-sw0-R c4) ▸
       at 1 2 (Toff301 ∷ Sw01 ∷ []) (wl0121 c4) ▸
       at 2 2 (Sb2-4-3-0 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑)) ▸
       at 3 2 (Toff301 ∷ Sw01 ∷ []) (wl0121 c4) ▸
       at 4 2 (Sb⁻2-4-3-0 ∷ Sw01 ∷ []) (c₂ (Swap) ((CS • CS • CS) ↑)) ▸
       at 0 5 (Sb2-4-01-3 ∷ []) (refl) ▸ done


-- comm CX40 TOFF213: 13 steps
lem-comm-CX40-TOFF213 : WsL → ⟪ (CX40 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CX40 ∷ []) ⟫ʷ
lem-comm-CX40-TOFF213 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX40 ∷ Toff213 ∷ []) (Sw34 ∷ Sw23 ∷ Toff314 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 6 3 (Toff214 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 5 3 (Toff314 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Toff324 ∷ Sw12 ∷ []) (wl0045 c4) ▸
       at 3 2 (Toff324 ∷ CX10 ∷ []) (c₂ (CX₁₀) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 2 2 (Toff314 ∷ Sw12 ∷ []) (wl0038 c4) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Toff314 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (Toff213 ∷ CX40 ∷ [])
  b1 = at 2 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0003 c4) ▸
       at 1 1 (Sw34 ∷ Toff213 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0004 c4) ▸
       at 1 7 (CX40 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm TOFF213 CX40: 13 steps
lem-comm-TOFF213-CX40 : WsL → ⟪ (Toff213 ∷ CX40 ∷ []) ⟫ʷ ≈ ⟪ (CX40 ∷ Toff213 ∷ []) ⟫ʷ
lem-comm-TOFF213-CX40 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff213 ∷ CX40 ∷ []) (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Toff314 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 3 (Toff214 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 2 3 (Toff314 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw12 ∷ Toff324 ∷ []) (sym (wl0038 c4)) ▸
       at 3 2 (CX10 ∷ Toff324 ∷ []) (sym (c₂ (CX₁₀) (K ↑ • CCZ • K ↑ • iI))) ▸
       at 4 2 (Sw12 ∷ Toff314 ∷ []) (sym (wl0045 c4)) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Toff314 ∷ Sw23 ∷ Sw34 ∷ []) (CX40 ∷ Toff213 ∷ [])
  b1 = at 5 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0003 c4) ▸
       at 6 1 (Sw34 ∷ Toff213 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0004 c4) ▸
       at 0 7 (CX40 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm push BOX(0;21) sw0 R: 3 steps
lem-comm-push-BOX⟨0·21⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Bx0-21 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-20 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·21⟩-sw0-R c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-21 ∷ []) (Bx1-20 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ12 ∷ []) (refl) ▸
       at 0 2 (CZ02 ∷ Sw01 ∷ []) (sym (wl0076 c4)) ▸
       at 0 1 (Bx1-20 ∷ []) (refl) ▸ done


-- comm push BOX(2;031) sw0 R: 8 steps
lem-comm-push-BOX⟨2·031⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Bx2-031 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-130 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨2·031⟩-sw0-R c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-031 ∷ []) (Bx2-130 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0135 c4)) ▸
       at 1 2 (Toff213 ∷ Sw01 ∷ []) (wl0136 c4) ▸
       at 2 2 (Bx1-20 ∷ Sw01 ∷ []) (lem-comm-push-BOX⟨0·21⟩-sw0-R c4) ▸
       at 3 2 (Toff213 ∷ Sw01 ∷ []) (wl0136 c4) ▸
       at 4 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0135 c4)) ▸
       at 5 2 (Bx1-20 ∷ Sw01 ∷ []) (lem-comm-push-BOX⟨0·21⟩-sw0-R c4) ▸
       at 0 6 (Bx2-130 ∷ []) (refl) ▸ done


-- comm push BOX(0;2431) sw0 R: 8 steps
lem-comm-push-BOX⟨0·2431⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2430 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·2431⟩-sw0-R c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-2431 ∷ []) (Bx1-2430 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx2-031 ∷ Toff024 ∷ CCZ024 ∷ Bx2-031 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw01 ∷ []) (lem-comm-push-CCZ024-sw0-R c4) ▸
       at 1 2 (Toff124 ∷ Sw01 ∷ []) (lem-comm-push-TOFF024-sw0-R c4) ▸
       at 2 2 (Bx2-130 ∷ Sw01 ∷ []) (lem-comm-push-BOX⟨2·031⟩-sw0-R c4) ▸
       at 3 2 (Toff124 ∷ Sw01 ∷ []) (lem-comm-push-TOFF024-sw0-R c4) ▸
       at 4 2 (CCZ124 ∷ Sw01 ∷ []) (lem-comm-push-CCZ024-sw0-R c4) ▸
       at 5 2 (Bx2-130 ∷ Sw01 ∷ []) (lem-comm-push-BOX⟨2·031⟩-sw0-R c4) ▸
       at 0 6 (Bx1-2430 ∷ []) (refl) ▸ done


-- comm push TOFF134 sw0 R: 86 steps
lem-comm-push-TOFF134-sw0-R : WsL → ⟪ (Sw01 ∷ Toff134 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-TOFF134-sw0-R c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (run b10))))))))))
  where
  b0 : Chain (Sw01 ∷ Toff134 ∷ []) (Sw01 ∷ Sw23 ∷ K1 ∷ CS24 ∷ CX12 ∷ Sw34 ∷ CS23⁻ ∷ Sw34 ∷ Sw34 ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw34 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Toff124 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Toff123 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (CS24 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸ done

  b1 : Chain (Sw01 ∷ Sw23 ∷ K1 ∷ CS24 ∷ CX12 ∷ Sw34 ∷ CS23⁻ ∷ Sw34 ∷ Sw34 ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw34 ∷ Sw23 ∷ []) (Sw01 ∷ K1 ∷ Sw23 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K1 ∷ ι1 ∷ Sw23 ∷ [])
  b1 = at 5 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 9 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 7 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 9 2 (ι1 ∷ Sw34 ∷ []) (sym (c₂ (iI ↑) (Swap ↑))) ▸
       at 10 2 [] (wl0004 c4) ▸
       at 1 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸ done

  b2 : Chain (Sw01 ∷ K1 ∷ Sw23 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K1 ∷ ι1 ∷ Sw23 ∷ []) (Sw01 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1 ∷ Sw23 ∷ ι1 ∷ Sw23 ∷ [])
  b2 = at 2 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0008 c4)) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 3 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0009 c4)) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 5 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS14 ∷ Sw23 ∷ []) (sym (wl0017 c4)) ▸
       at 7 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸ done

  b3 : Chain (Sw01 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1 ∷ Sw23 ∷ ι1 ∷ Sw23 ∷ []) (K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Sw01 ∷ K1 ∷ ι1 ∷ [])
  b3 = at 8 2 (ι1 ∷ Sw23 ∷ []) (sym (c₂ (iI ↑) (Swap))) ▸
       at 9 2 [] (wl0003 c4) ▸
       at 0 2 (K0 ∷ Sw01 ∷ []) (sym (wl0026 c4)) ▸
       at 1 2 (CS34 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑)) ▸
       at 2 2 (CX03 ∷ Sw01 ∷ []) (sym (wl0016 c4)) ▸
       at 3 2 (CS34⁻ ∷ Sw01 ∷ []) (c₂ (Swap) ((CS • CS • CS) ↑)) ▸
       at 4 2 (CX03 ∷ Sw01 ∷ []) (sym (wl0016 c4)) ▸
       at 5 2 (CS04 ∷ Sw01 ∷ []) (lem-comm-push-CS14-sw0-R c4) ▸ done

  b4 : Chain (K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Sw01 ∷ K1 ∷ ι1 ∷ []) (Sw23 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ Sw23 ∷ CX03 ∷ CS04 ∷ K0 ∷ ι1 ∷ Sw01 ∷ [])
  b4 = at 6 2 (K0 ∷ Sw01 ∷ []) (sym (wl0026 c4)) ▸
       at 7 2 (ι1 ∷ Sw01 ∷ []) (wl0118 c4) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 2 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0011 c4)) ▸
       at 4 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0003 c4) ▸
       at 4 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0012 c4)) ▸ done

  b5 : Chain (Sw23 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ Sw23 ∷ CX03 ∷ CS04 ∷ K0 ∷ ι1 ∷ Sw01 ∷ []) (Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ Sw12 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0 ∷ ι1 ∷ Sw23 ∷ Sw01 ∷ [])
  b5 = at 6 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0003 c4) ▸
       at 6 2 (CS04 ∷ Sw23 ∷ []) (lem-comm-push-CS04-sw2-R c4) ▸
       at 7 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 8 2 (ι1 ∷ Sw23 ∷ []) (sym (c₂ (iI ↑) (Swap))) ▸
       at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 2 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 3 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 c4)) ▸ done

  b6 : Chain (Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ Sw12 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0 ∷ ι1 ∷ Sw23 ∷ Sw01 ∷ []) (Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι1 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ [])
  b6 = at 5 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0006 c4) ▸
       at 5 2 (CS14⁻ ∷ Sw12 ∷ []) (sym (wl0014 c4)) ▸
       at 7 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0006 c4) ▸
       at 7 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R c4) ▸
       at 8 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 9 2 (ι1 ∷ Sw12 ∷ []) (wl0119 c4) ▸ done

  b7 : Chain (Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι1 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw34 ∷ CS04 ∷ K0 ∷ ι1 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ [])
  b7 = at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 5 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0004 c4) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0004 c4) ▸
       at 7 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸ done

  b8 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw34 ∷ CS04 ∷ K0 ∷ ι1 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι1 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ [])
  b8 = at 9 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0004 c4) ▸
       at 9 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 10 2 (ι1 ∷ Sw34 ∷ []) (sym (c₂ (iI ↑) (Swap ↑))) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0003 c4) ▸ done

  b9 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι1 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι1 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ [])
  b9 = at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0003 c4) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (wl0003 c4) ▸
       at 10 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 11 2 (ι1 ∷ Sw23 ∷ []) (sym (c₂ (iI ↑) (Swap))) ▸ done

  b10 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι1 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ []) (Toff034 ∷ Sw01 ∷ [])
  b10 = at 4 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (sym (wl0125 c4)) ▸
       at 4 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff014 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff024 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff034 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm push SBOX(0;2;1;3) sw0 R: 3 steps
lem-comm-push-SBOX⟨0·2·1·3⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Sb0-2-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-0-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨0·2·1·3⟩-sw0-R c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb0-2-1-3 ∷ []) (Sb1-2-0-3 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS12 ∷ []) (refl) ▸
       at 0 2 (CS02 ∷ Sw01 ∷ []) (sym (wl0024 c4)) ▸
       at 0 1 (Sb1-2-0-3 ∷ []) (refl) ▸ done


-- comm push SBOXd(0;2;1;3) sw0 R: 3 steps
lem-comm-push-SBOXd⟨0·2·1·3⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Sb⁻0-2-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-2-0-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨0·2·1·3⟩-sw0-R c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻0-2-1-3 ∷ []) (Sb⁻1-2-0-3 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 2 (CS02⁻ ∷ Sw01 ∷ []) (sym (wl0023 c4)) ▸
       at 0 1 (Sb⁻1-2-0-3 ∷ []) (refl) ▸ done


-- comm push SBOX(0;2;43;1) sw0 R: 7 steps
lem-comm-push-SBOX⟨0·2·43·1⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-43-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨0·2·43·1⟩-sw0-R c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb0-2-43-1 ∷ []) (Sb1-2-43-0 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 0 2 (Bx1-2430 ∷ Sw01 ∷ []) (lem-comm-push-BOX⟨0·2431⟩-sw0-R c4) ▸
       at 1 2 (Toff034 ∷ Sw01 ∷ []) (lem-comm-push-TOFF134-sw0-R c4) ▸
       at 2 2 (Sb1-2-0-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·2·1·3⟩-sw0-R c4) ▸
       at 3 2 (Toff034 ∷ Sw01 ∷ []) (lem-comm-push-TOFF134-sw0-R c4) ▸
       at 4 2 (Sb⁻1-2-0-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOXd⟨0·2·1·3⟩-sw0-R c4) ▸
       at 0 5 (Sb1-2-43-0 ∷ []) (refl) ▸ done


-- comm push BOX(1;20) sw1 R: 4 steps
lem-comm-push-BOX⟨1·20⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Bx1-20 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-10 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨1·20⟩-sw1-R c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-20 ∷ []) (Bx2-10 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ02 ∷ []) (refl) ▸
       at 1 1 (Sw12 ∷ CZ01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0006 c4) ▸
       at 0 1 (Bx2-10 ∷ []) (refl) ▸ done


-- comm push BOX(2;130) sw1 R: 8 steps
lem-comm-push-BOX⟨2·130⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Bx2-130 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-230 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨2·130⟩-sw1-R c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-130 ∷ []) (Bx1-230 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff213 ∷ Bx1-20 ∷ Toff213 ∷ CCZ123 ∷ Bx1-20 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw12 ∷ []) (sym (wl0137 c4)) ▸
       at 1 2 (Toff123 ∷ Sw12 ∷ []) (wl0138 c4) ▸
       at 2 2 (Bx2-10 ∷ Sw12 ∷ []) (lem-comm-push-BOX⟨1·20⟩-sw1-R c4) ▸
       at 3 2 (Toff123 ∷ Sw12 ∷ []) (wl0138 c4) ▸
       at 4 2 (CCZ123 ∷ Sw12 ∷ []) (sym (wl0137 c4)) ▸
       at 5 2 (Bx2-10 ∷ Sw12 ∷ []) (lem-comm-push-BOX⟨1·20⟩-sw1-R c4) ▸
       at 0 6 (Bx1-230 ∷ []) (refl) ▸ done


-- comm push BOX(1;2430) sw1 R: 8 steps
lem-comm-push-BOX⟨1·2430⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Bx1-2430 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1430 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨1·2430⟩-sw1-R c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-2430 ∷ []) (Bx2-1430 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff124 ∷ Bx2-130 ∷ Toff124 ∷ CCZ124 ∷ Bx2-130 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0122 c4)) ▸
       at 1 2 (Toff214 ∷ Sw12 ∷ []) (wl0123 c4) ▸
       at 2 2 (Bx1-230 ∷ Sw12 ∷ []) (lem-comm-push-BOX⟨2·130⟩-sw1-R c4) ▸
       at 3 2 (Toff214 ∷ Sw12 ∷ []) (wl0123 c4) ▸
       at 4 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0122 c4)) ▸
       at 5 2 (Bx1-230 ∷ Sw12 ∷ []) (lem-comm-push-BOX⟨2·130⟩-sw1-R c4) ▸
       at 0 6 (Bx2-1430 ∷ []) (refl) ▸ done


-- comm push SBOX(1;2;0;3) sw1 R: 4 steps
lem-comm-push-SBOX⟨1·2·0·3⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Sb1-2-0-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-0-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨1·2·0·3⟩-sw1-R c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb1-2-0-3 ∷ []) (Sb2-1-0-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS02 ∷ []) (refl) ▸
       at 1 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0006 c4) ▸
       at 0 1 (Sb2-1-0-3 ∷ []) (refl) ▸ done


-- comm push SBOXd(1;2;0;3) sw1 R: 4 steps
lem-comm-push-SBOXd⟨1·2·0·3⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Sb⁻1-2-0-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-1-0-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨1·2·0·3⟩-sw1-R c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻1-2-0-3 ∷ []) (Sb⁻2-1-0-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS02⁻ ∷ []) (refl) ▸
       at 1 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0006 c4) ▸
       at 0 1 (Sb⁻2-1-0-3 ∷ []) (refl) ▸ done


-- comm push SBOX(1;2;43;0) sw1 R: 7 steps
lem-comm-push-SBOX⟨1·2·43·0⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Sb1-2-43-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-43-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨1·2·43·0⟩-sw1-R c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb1-2-43-0 ∷ []) (Sb2-1-43-0 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx1-2430 ∷ Toff034 ∷ Sb1-2-0-3 ∷ Toff034 ∷ Sb⁻1-2-0-3 ∷ []) (refl) ▸
       at 0 2 (Bx2-1430 ∷ Sw12 ∷ []) (lem-comm-push-BOX⟨1·2430⟩-sw1-R c4) ▸
       at 1 2 (Toff034 ∷ Sw12 ∷ []) (lem-comm-push-TOFF034-sw1-R c4) ▸
       at 2 2 (Sb2-1-0-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·2·0·3⟩-sw1-R c4) ▸
       at 3 2 (Toff034 ∷ Sw12 ∷ []) (lem-comm-push-TOFF034-sw1-R c4) ▸
       at 4 2 (Sb⁻2-1-0-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOXd⟨1·2·0·3⟩-sw1-R c4) ▸
       at 0 5 (Sb2-1-43-0 ∷ []) (refl) ▸ done


-- comm push BOX(1;230) sw2 R: 8 steps
lem-comm-push-BOX⟨1·230⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Bx1-230 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-320 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨1·230⟩-sw2-R c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-230 ∷ []) (Bx1-320 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff123 ∷ Bx2-10 ∷ Toff123 ∷ CCZ123 ∷ Bx2-10 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw23 ∷ []) (sym (wl0139 c4)) ▸
       at 1 2 (Toff123 ∷ Sw23 ∷ []) (wl0140 c4) ▸
       at 2 2 (Bx2-10 ∷ Sw23 ∷ []) (sym (c₂ (CZ) (Swap))) ▸
       at 3 2 (Toff123 ∷ Sw23 ∷ []) (wl0140 c4) ▸
       at 4 2 (CCZ123 ∷ Sw23 ∷ []) (sym (wl0139 c4)) ▸
       at 5 2 (Bx2-10 ∷ Sw23 ∷ []) (sym (c₂ (CZ) (Swap))) ▸
       at 0 6 (Bx1-320 ∷ []) (refl) ▸ done


-- comm push BOX(2;1430) sw2 R: 12 steps
lem-comm-push-BOX⟨2·1430⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Bx2-1430 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1420 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨2·1430⟩-sw2-R c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw23 ∷ Bx2-1430 ∷ []) (CCZ134 ∷ Toff314 ∷ Bx1-320 ∷ Toff314 ∷ Sw23 ∷ CCZ124 ∷ Bx1-230 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff214 ∷ Bx1-230 ∷ Toff214 ∷ CCZ124 ∷ Bx1-230 ∷ []) (refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 0 3 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (Toff314 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Bx1-320 ∷ Sw23 ∷ []) (lem-comm-push-BOX⟨1·230⟩-sw2-R c4) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 3 3 (Toff314 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (CCZ134 ∷ Toff314 ∷ Bx1-320 ∷ Toff314 ∷ Sw23 ∷ CCZ124 ∷ Bx1-230 ∷ []) (Bx3-1420 ∷ Sw23 ∷ [])
  b1 = at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Bx1-320 ∷ Sw23 ∷ []) (lem-comm-push-BOX⟨1·230⟩-sw2-R c4) ▸
       at 0 6 (Bx3-1420 ∷ []) (refl) ▸ done


-- comm push SBOX(2;1;43;0) sw2 R: 9 steps
lem-comm-push-SBOX⟨2·1·43·0⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Sb2-1-43-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-1-42-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨2·1·43·0⟩-sw2-R c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw23 ∷ Sb2-1-43-0 ∷ []) (Bx3-1420 ∷ Toff024 ∷ Sb2-1-0-3 ∷ Toff024 ∷ Sb⁻2-1-0-3 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx2-1430 ∷ Toff034 ∷ Sb2-1-0-3 ∷ Toff034 ∷ Sb⁻2-1-0-3 ∷ []) (refl) ▸
       at 0 2 (Bx3-1420 ∷ Sw23 ∷ []) (lem-comm-push-BOX⟨2·1430⟩-sw2-R c4) ▸
       at 2 1 (Sw23 ∷ Toff024 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0003 c4) ▸
       at 2 2 (Sb2-1-0-3 ∷ Sw23 ∷ []) (sym (c₂ (CS) (Swap))) ▸
       at 4 1 (Sw23 ∷ Toff024 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0003 c4) ▸
       at 4 2 (Sb⁻2-1-0-3 ∷ Sw23 ∷ []) (sym (c₂ (CS • CS • CS) (Swap))) ▸ done

  b1 : Chain (Bx3-1420 ∷ Toff024 ∷ Sb2-1-0-3 ∷ Toff024 ∷ Sb⁻2-1-0-3 ∷ Sw23 ∷ []) (Sb3-1-42-0 ∷ Sw23 ∷ [])
  b1 = at 0 5 (Sb3-1-42-0 ∷ []) (refl) ▸ done


-- comm push BOX(1;320) sw3 R: 12 steps
lem-comm-push-BOX⟨1·320⟩-sw3-R : WsL → ⟪ (Sw34 ∷ Bx1-320 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-420 ∷ Sw34 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨1·320⟩-sw3-R c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw34 ∷ Bx1-320 ∷ []) (CCZ124 ∷ Toff124 ∷ Bx3-10 ∷ Toff124 ∷ Sw34 ∷ CCZ123 ∷ Bx3-10 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff123 ∷ Bx3-10 ∷ Toff123 ∷ CCZ123 ∷ Bx3-10 ∷ []) (refl) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 0 3 (CCZ124 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 3 (Toff124 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Bx3-10 ∷ Sw34 ∷ []) (sym (c₂ (CZ) (Swap ↑))) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (Toff124 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (CCZ124 ∷ Toff124 ∷ Bx3-10 ∷ Toff124 ∷ Sw34 ∷ CCZ123 ∷ Bx3-10 ∷ []) (Bx1-420 ∷ Sw34 ∷ [])
  b1 = at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 4 3 (CCZ124 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Bx3-10 ∷ Sw34 ∷ []) (sym (c₂ (CZ) (Swap ↑))) ▸
       at 0 6 (Bx1-420 ∷ []) (refl) ▸ done


-- comm push BOX(3;1420) sw3 R: 8 steps
lem-comm-push-BOX⟨3·1420⟩-sw3-R : WsL → ⟪ (Sw34 ∷ Bx3-1420 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1320 ∷ Sw34 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨3·1420⟩-sw3-R c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx3-1420 ∷ []) (Bx4-1320 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff314 ∷ Bx1-320 ∷ Toff314 ∷ CCZ134 ∷ Bx1-320 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw34 ∷ []) (sym (wl0141 c4)) ▸
       at 1 2 (Toff413 ∷ Sw34 ∷ []) (wl0142 c4) ▸
       at 2 2 (Bx1-420 ∷ Sw34 ∷ []) (lem-comm-push-BOX⟨1·320⟩-sw3-R c4) ▸
       at 3 2 (Toff413 ∷ Sw34 ∷ []) (wl0142 c4) ▸
       at 4 2 (CCZ134 ∷ Sw34 ∷ []) (sym (wl0141 c4)) ▸
       at 5 2 (Bx1-420 ∷ Sw34 ∷ []) (lem-comm-push-BOX⟨1·320⟩-sw3-R c4) ▸
       at 0 6 (Bx4-1320 ∷ []) (refl) ▸ done


-- comm push TOFF024 sw3 R: 76 steps
lem-comm-push-TOFF024-sw3-R : WsL → ⟪ (Sw34 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ Sw34 ∷ []) ⟫ʷ
lem-comm-push-TOFF024-sw3-R c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (run b9)))))))))
  where
  b0 : Chain (Sw34 ∷ Toff024 ∷ []) (Sw34 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Toff014 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸ done

  b1 : Chain (Sw34 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) (Sw34 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ [])
  b1 = at 8 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 10 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 11 2 [] (wl0003 c4) ▸ done

  b2 : Chain (Sw34 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ []) (Sw34 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ [])
  b2 = at 2 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 5 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 9 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸ done

  b3 : Chain (Sw34 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ []) (Sw34 ∷ K0 ∷ CS24 ∷ CX02 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ [])
  b3 = at 7 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 9 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 10 2 [] (wl0004 c4) ▸
       at 1 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 2 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0005 c4)) ▸
       at 5 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 3 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (Sw34 ∷ K0 ∷ CS24 ∷ CX02 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ []) (K0 ∷ Sw34 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0 ∷ ι ∷ [])
  b4 = at 4 2 (CS24⁻ ∷ Sw12 ∷ []) (sym (wl0007 c4)) ▸
       at 7 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 5 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R c4) ▸
       at 7 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 8 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 9 2 [] (wl0006 c4) ▸
       at 0 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸ done

  b5 : Chain (K0 ∷ Sw34 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0 ∷ ι ∷ []) (K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw34 ∷ K0 ∷ ι ∷ [])
  b5 = at 2 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0004 c4) ▸
       at 2 2 (CX02 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap))) ▸
       at 4 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0004 c4) ▸
       at 4 2 (CX02 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap))) ▸
       at 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0004 c4) ▸ done

  b6 : Chain (K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw34 ∷ K0 ∷ ι ∷ []) (Sw12 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw12 ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ [])
  b6 = at 6 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 7 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 1 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 2 2 (CS13 ∷ Sw12 ∷ []) (sym (wl0046 c4)) ▸
       at 4 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0006 c4) ▸
       at 4 2 (CS13⁻ ∷ Sw12 ∷ []) (sym (wl0028 c4)) ▸ done

  b7 : Chain (Sw12 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw12 ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ []) (Sw12 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw34 ∷ [])
  b7 = at 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0006 c4) ▸
       at 6 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 7 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 8 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 2 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b8 : Chain (Sw12 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw34 ∷ []) (Sw12 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ Sw23 ∷ ι ∷ Sw12 ∷ Sw34 ∷ [])
  b8 = at 3 2 [] (wl0003 c4) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0003 c4) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0003 c4) ▸
       at 8 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸ done

  b9 : Chain (Sw12 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ Sw23 ∷ ι ∷ Sw12 ∷ Sw34 ∷ []) (Toff023 ∷ Sw34 ∷ [])
  b9 = at 9 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 2 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff023 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm push SBOX(3;1;42;0) sw3 R: 7 steps
lem-comm-push-SBOX⟨3·1·42·0⟩-sw3-R : WsL → ⟪ (Sw34 ∷ Sb3-1-42-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-1-32-0 ∷ Sw34 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨3·1·42·0⟩-sw3-R c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb3-1-42-0 ∷ []) (Sb4-1-32-0 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx3-1420 ∷ Toff024 ∷ Sb3-1-0-2 ∷ Toff024 ∷ Sb⁻3-1-0-2 ∷ []) (refl) ▸
       at 0 2 (Bx4-1320 ∷ Sw34 ∷ []) (lem-comm-push-BOX⟨3·1420⟩-sw3-R c4) ▸
       at 1 2 (Toff023 ∷ Sw34 ∷ []) (lem-comm-push-TOFF024-sw3-R c4) ▸
       at 2 2 (Sb3-1-0-2 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 3 2 (Toff023 ∷ Sw34 ∷ []) (lem-comm-push-TOFF024-sw3-R c4) ▸
       at 4 2 (Sb⁻3-1-0-2 ∷ Sw34 ∷ []) (sym (c₂ (CS • CS • CS) (Swap ↑))) ▸
       at 0 5 (Sb4-1-32-0 ∷ []) (refl) ▸ done


-- comm push BOX(1;420) sw2 R: 12 steps
lem-comm-push-BOX⟨1·420⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Bx1-420 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-430 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨1·420⟩-sw2-R c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw23 ∷ Bx1-420 ∷ []) (CCZ134 ∷ Toff134 ∷ Bx4-10 ∷ Toff134 ∷ Sw23 ∷ CCZ124 ∷ Bx4-10 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff124 ∷ Bx4-10 ∷ Toff124 ∷ CCZ124 ∷ Bx4-10 ∷ []) (refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 0 3 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (Toff134 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Bx4-10 ∷ Sw23 ∷ []) (sym (c₂ (CZ) (Swap))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 3 3 (Toff134 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (CCZ134 ∷ Toff134 ∷ Bx4-10 ∷ Toff134 ∷ Sw23 ∷ CCZ124 ∷ Bx4-10 ∷ []) (Bx1-430 ∷ Sw23 ∷ [])
  b1 = at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Bx4-10 ∷ Sw23 ∷ []) (sym (c₂ (CZ) (Swap))) ▸
       at 0 6 (Bx1-430 ∷ []) (refl) ▸ done


-- comm push BOX(4;1320) sw2 R: 12 steps
lem-comm-push-BOX⟨4·1320⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Bx4-1320 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1230 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨4·1320⟩-sw2-R c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw23 ∷ Bx4-1320 ∷ []) (CCZ124 ∷ Toff412 ∷ Bx1-430 ∷ Toff412 ∷ Sw23 ∷ CCZ134 ∷ Bx1-420 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff413 ∷ Bx1-420 ∷ Toff413 ∷ CCZ134 ∷ Bx1-420 ∷ []) (refl) ▸
       at 1 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0003 c4) ▸
       at 2 1 (Sw23 ∷ Toff412 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0003 c4) ▸
       at 2 2 (Bx1-430 ∷ Sw23 ∷ []) (lem-comm-push-BOX⟨1·420⟩-sw2-R c4) ▸
       at 4 1 (Sw23 ∷ Toff412 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0003 c4) ▸ done

  b1 : Chain (CCZ124 ∷ Toff412 ∷ Bx1-430 ∷ Toff412 ∷ Sw23 ∷ CCZ134 ∷ Bx1-420 ∷ []) (Bx4-1230 ∷ Sw23 ∷ [])
  b1 = at 5 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0003 c4) ▸
       at 5 2 (Bx1-430 ∷ Sw23 ∷ []) (lem-comm-push-BOX⟨1·420⟩-sw2-R c4) ▸
       at 0 6 (Bx4-1230 ∷ []) (refl) ▸ done


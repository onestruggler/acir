{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R005 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL ; wl0001 ; wl0002 ; wl0006 ; wl0007 ; wl0008 ; wl0009 ; wl0010 ; wl0013 ; wl0019 ; wl0021 ; wl0022 ; wl0023 ; wl0030 ; wl0032 ; wl0033 ; wl0037 ; wl0038 ; wl0044 ; wl0047 ; wl0048 ; wl0056 ; wl0057 ; wl0058 ; wl0059 ; wl0060 ; wl0061 ; wl0063 ; wl0065 ; wl0066 ; wl0067 ; wl0068 ; wl0070 ; wl0076 ; wl0078 ; wl0088 ; wl0090 ; wl0092 ; wl0093 ; wl0094 ; wl0095 ; wl0096 ; wl0097 ; wl0098 ; wl0099 ; wl0100 ; wl0101 ; wl0102)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-nat-1-CCZ023 ; lem-nat-1-CCZ024 ; lem-nat-1-TOFF014 ; lem-nat-1-TOFF024 ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ013 ; lem-nat-2-CCZ024 ; lem-nat-2-CCZ034 ; lem-nat-2-TOFF012 ; lem-nat-2-TOFF013 ; lem-nat-2-TOFF024 ; lem-nat-2-TOFF034 ; lem-nat-2-TOFF301 ; lem-nat-3-CCZ024)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-0-CCZ024 ; lem-nat-0-CCZ124 ; lem-nat-1-CCZ013 ; lem-nat-1-CCZ014 ; lem-nat-1-TOFF301 ; lem-nat-1-TOFF302 ; lem-nat-2-CCZ124 ; lem-nat-2-TOFF201 ; lem-nat-2-TOFF204 ; lem-nat-2-TOFF304 ; lem-nat-3-BOX⟨0·14⟩ ; lem-nat-3-CCZ013 ; lem-nat-3-CCZ023 ; lem-nat-3-TOFF203 ; lem-nat-3-TOFF204)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-0-CCZ014 ; lem-nat-0-TOFF014 ; lem-nat-0-TOFF104 ; lem-nat-1-TOFF104 ; lem-nat-1-TOFF204)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-BOX⟨0·43⟩ ; lem-nat-0-CZ04 ; lem-nat-0-CZ14 ; lem-nat-0-TOFF214 ; lem-nat-0-TOFF402 ; lem-nat-1-BOX⟨1·43⟩ ; lem-nat-1-TOFF013 ; lem-nat-2-BOX⟨2·43⟩)
-- nat 0 TOFF024: 70 steps
lem-nat-0-TOFF024 : WsL → ⟪ (Sw01 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff124 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-TOFF024 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (run b8))))))))
  where
  b0 : Chain (Sw01 ∷ Toff024 ∷ []) (Sw01 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Toff014 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸ done

  b1 : Chain (Sw01 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) (Sw01 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ [])
  b1 = at 8 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 10 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 11 2 [] (wl0006 c4) ▸ done

  b2 : Chain (Sw01 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ []) (Sw01 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ [])
  b2 = at 2 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 3 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 5 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 9 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸ done

  b3 : Chain (Sw01 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ []) (Sw01 ∷ K0 ∷ CS24 ∷ CX02 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ [])
  b3 = at 7 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 9 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 10 2 [] (wl0007 c4) ▸
       at 1 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 2 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 c4)) ▸
       at 5 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 3 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (Sw01 ∷ K0 ∷ CS24 ∷ CX02 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ []) (Sw01 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ Sw12 ∷ K0 ∷ ι ∷ Sw12 ∷ [])
  b4 = at 4 2 (CS24⁻ ∷ Sw12 ∷ []) (sym (wl0009 c4)) ▸
       at 7 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 5 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 7 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸
       at 8 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done

  b5 : Chain (Sw01 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ Sw12 ∷ K0 ∷ ι ∷ Sw12 ∷ []) (K1 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ Sw01 ∷ CS04 ∷ K0 ∷ ι ∷ [])
  b5 = at 7 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 8 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 9 2 [] (wl0001 c4) ▸
       at 0 2 (K1 ∷ Sw01 ∷ []) (sym (wl0076 c4)) ▸
       at 1 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 2 2 (CX12 ∷ Sw01 ∷ []) (sym (wl0060 c4)) ▸
       at 3 2 (CS24⁻ ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • (CS • CS • CS) • Swap ↑)) ▸
       at 4 2 (CX12 ∷ Sw01 ∷ []) (sym (wl0060 c4)) ▸ done

  b6 : Chain (K1 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ Sw01 ∷ CS04 ∷ K0 ∷ ι ∷ []) (Sw34 ∷ Sw34 ∷ K1 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K1 ∷ ι ∷ Sw01 ∷ [])
  b6 = at 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 6 2 (CS13 ∷ Sw01 ∷ []) (sym (wl0061 c4)) ▸
       at 7 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 5 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K1 ∷ Sw01 ∷ []) (sym (wl0076 c4)) ▸
       at 7 2 (ι ∷ Sw01 ∷ []) (wl0030 c4) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸ done

  b7 : Chain (Sw34 ∷ Sw34 ∷ K1 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K1 ∷ ι ∷ Sw01 ∷ []) (Sw34 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw34 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ K1 ∷ ι ∷ Sw01 ∷ [])
  b7 = at 1 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 3 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0007 c4) ▸
       at 3 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 5 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0007 c4) ▸
       at 5 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 7 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b8 : Chain (Sw34 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw34 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ K1 ∷ ι ∷ Sw01 ∷ []) (Toff124 ∷ Sw01 ∷ [])
  b8 = at 6 2 [] (wl0007 c4) ▸
       at 7 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 8 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 1 8 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (wl0032 c4) ▸
       at 1 8 (Toff123 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff124 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 TOFF401: 75 steps
lem-nat-0-TOFF401 : WsL → ⟪ (Sw01 ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-TOFF401 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (run b9)))))))))
  where
  b0 : Chain (Sw01 ∷ Toff401 ∷ []) (Sw01 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Toff301 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (K3 ∷ Sw23 ∷ []) (sym (wl0057 c4)) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸ done

  b1 : Chain (Sw01 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw34 ∷ []) (Sw01 ∷ K4 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ [])
  b1 = at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K3 ∷ Sw23 ∷ []) (sym (wl0057 c4)) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 10 2 [] (wl0006 c4) ▸
       at 1 2 (K4 ∷ Sw34 ∷ []) (sym (wl0067 c4)) ▸ done

  b2 : Chain (Sw01 ∷ K4 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ []) (Sw01 ∷ K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw34 ∷ K3 ∷ ι ∷ Sw34 ∷ [])
  b2 = at 4 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 2 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 4 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (Sw01 ∷ K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw34 ∷ K3 ∷ ι ∷ Sw34 ∷ []) (K4 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw01 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K4 ∷ ι ∷ [])
  b3 = at 7 2 (K4 ∷ Sw34 ∷ []) (sym (wl0067 c4)) ▸
       at 8 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 9 2 [] (wl0007 c4) ▸
       at 0 2 (K4 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ ↑)) ▸
       at 2 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 2 2 (CS03 ∷ Sw01 ∷ []) (sym (wl0019 c4)) ▸
       at 3 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸ done

  b4 : Chain (K4 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw01 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K4 ∷ ι ∷ []) (K4 ∷ CS04 ∷ CX10 ∷ CS04⁻ ∷ CX10 ∷ Sw01 ∷ CS04 ∷ K4 ∷ ι ∷ [])
  b4 = at 1 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CX10 ∷ Sw01 ∷ []) (sym (wl0070 c4)) ▸
       at 4 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 4 2 (CS03⁻ ∷ Sw01 ∷ []) (sym (wl0022 c4)) ▸
       at 5 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 3 3 (CS04⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX10 ∷ Sw01 ∷ []) (sym (wl0070 c4)) ▸ done

  b5 : Chain (K4 ∷ CS04 ∷ CX10 ∷ CS04⁻ ∷ CX10 ∷ Sw01 ∷ CS04 ∷ K4 ∷ ι ∷ []) (Sw34 ∷ Sw34 ∷ K4 ∷ CS04 ∷ CX10 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ K4 ∷ ι ∷ Sw01 ∷ [])
  b5 = at 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 6 2 (CS13 ∷ Sw01 ∷ []) (sym (wl0061 c4)) ▸
       at 7 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 5 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K4 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ ↑)) ▸
       at 7 2 (ι ∷ Sw01 ∷ []) (wl0030 c4) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸ done

  b6 : Chain (Sw34 ∷ Sw34 ∷ K4 ∷ CS04 ∷ CX10 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ K4 ∷ ι ∷ Sw01 ∷ []) (Sw34 ∷ K3 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ Sw34 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ K4 ∷ ι ∷ Sw01 ∷ [])
  b6 = at 1 2 (K3 ∷ Sw34 ∷ []) (sym (wl0068 c4)) ▸
       at 3 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0007 c4) ▸
       at 3 2 (CX10 ∷ Sw34 ∷ []) (sym (c₂ (CX₁₀) (Swap ↑))) ▸
       at 5 1 (Sw34 ∷ CS03⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0007 c4) ▸
       at 5 2 (CX10 ∷ Sw34 ∷ []) (sym (c₂ (CX₁₀) (Swap ↑))) ▸
       at 7 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b7 : Chain (Sw34 ∷ K3 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ Sw34 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ K4 ∷ ι ∷ Sw01 ∷ []) (Sw34 ∷ Sw23 ∷ K2 ∷ CS02 ∷ CX10 ∷ Sw23 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw01 ∷ [])
  b7 = at 6 2 [] (wl0007 c4) ▸
       at 7 2 (K3 ∷ Sw34 ∷ []) (sym (wl0068 c4)) ▸
       at 8 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 2 2 (K2 ∷ Sw23 ∷ []) (sym (wl0058 c4)) ▸
       at 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0006 c4) ▸
       at 4 2 (CX10 ∷ Sw23 ∷ []) (sym (c₂ (CX₁₀) (Swap))) ▸ done

  b8 : Chain (Sw34 ∷ Sw23 ∷ K2 ∷ CS02 ∷ CX10 ∷ Sw23 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw01 ∷ []) (Sw34 ∷ Sw23 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw01 ∷ [])
  b8 = at 6 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0006 c4) ▸
       at 6 2 (CX10 ∷ Sw23 ∷ []) (sym (c₂ (CX₁₀) (Swap))) ▸
       at 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0006 c4) ▸
       at 8 2 (K2 ∷ Sw23 ∷ []) (sym (wl0058 c4)) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 2 8 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (wl0094 c4) ▸ done

  b9 : Chain (Sw34 ∷ Sw23 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw01 ∷ []) (Toff401 ∷ Sw01 ∷ [])
  b9 = at 2 8 (Toff201 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff301 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff401 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 BOX(4;013): 8 steps
lem-nat-0-BOX⟨4·013⟩ : WsL → ⟪ (Sw01 ∷ Bx4-013 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-103 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·013⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-013 ∷ []) (Bx4-103 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff401 ∷ Bx0-43 ∷ Toff401 ∷ CCZ014 ∷ Bx0-43 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 1 2 (Toff401 ∷ Sw01 ∷ []) (lem-nat-0-TOFF401 c4) ▸
       at 2 2 (Bx1-43 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·43⟩ c4) ▸
       at 3 2 (Toff401 ∷ Sw01 ∷ []) (lem-nat-0-TOFF401 c4) ▸
       at 4 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 5 2 (Bx1-43 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·43⟩ c4) ▸
       at 0 6 (Bx4-103 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;4213): 8 steps
lem-nat-0-BOX⟨0·4213⟩ : WsL → ⟪ (Sw01 ∷ Bx0-4213 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-4203 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·4213⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-4213 ∷ []) (Bx1-4203 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx4-013 ∷ Toff024 ∷ CCZ024 ∷ Bx4-013 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 1 2 (Toff124 ∷ Sw01 ∷ []) (lem-nat-0-TOFF024 c4) ▸
       at 2 2 (Bx4-103 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·013⟩ c4) ▸
       at 3 2 (Toff124 ∷ Sw01 ∷ []) (lem-nat-0-TOFF024 c4) ▸
       at 4 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 5 2 (Bx4-103 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·013⟩ c4) ▸
       at 0 6 (Bx1-4203 ∷ []) (refl) ▸ done


-- nat 1 TOFF401: 2 steps
lem-nat-1-TOFF401 : WsL → ⟪ (Sw12 ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-TOFF401 c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Toff401 ∷ []) (Toff402 ∷ Sw12 ∷ [])
  b0 = at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 0 3 (Toff402 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 1 BOX(4;103): 8 steps
lem-nat-1-BOX⟨4·103⟩ : WsL → ⟪ (Sw12 ∷ Bx4-103 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-203 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·103⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-103 ∷ []) (Bx4-203 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff401 ∷ Bx1-43 ∷ Toff401 ∷ CCZ014 ∷ Bx1-43 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 1 2 (Toff402 ∷ Sw12 ∷ []) (lem-nat-1-TOFF401 c4) ▸
       at 2 2 (Bx2-43 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·43⟩ c4) ▸
       at 3 2 (Toff402 ∷ Sw12 ∷ []) (lem-nat-1-TOFF401 c4) ▸
       at 4 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 5 2 (Bx2-43 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·43⟩ c4) ▸
       at 0 6 (Bx4-203 ∷ []) (refl) ▸ done


-- nat 1 BOX(1;4203): 8 steps
lem-nat-1-BOX⟨1·4203⟩ : WsL → ⟪ (Sw12 ∷ Bx1-4203 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4103 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·4203⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-4203 ∷ []) (Bx2-4103 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff124 ∷ Bx4-103 ∷ Toff124 ∷ CCZ124 ∷ Bx4-103 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0078 c4)) ▸
       at 1 2 (Toff214 ∷ Sw12 ∷ []) (wl0095 c4) ▸
       at 2 2 (Bx4-203 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·103⟩ c4) ▸
       at 3 2 (Toff214 ∷ Sw12 ∷ []) (wl0095 c4) ▸
       at 4 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0078 c4)) ▸
       at 5 2 (Bx4-203 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·103⟩ c4) ▸
       at 0 6 (Bx2-4103 ∷ []) (refl) ▸ done


-- nat 2 TOFF214: 2 steps
lem-nat-2-TOFF214 : WsL → ⟪ (Sw23 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-TOFF214 c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Toff214 ∷ []) (Toff314 ∷ Sw23 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 0 3 (Toff314 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 TOFF402: 2 steps
lem-nat-2-TOFF402 : WsL → ⟪ (Sw23 ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-TOFF402 c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Toff402 ∷ []) (Toff403 ∷ Sw23 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 0 3 (Toff403 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 BOX(4;203): 8 steps
lem-nat-2-BOX⟨4·203⟩ : WsL → ⟪ (Sw23 ∷ Bx4-203 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-302 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·203⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-203 ∷ []) (Bx4-302 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff402 ∷ Bx2-43 ∷ Toff402 ∷ CCZ024 ∷ Bx2-43 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 1 2 (Toff403 ∷ Sw23 ∷ []) (lem-nat-2-TOFF402 c4) ▸
       at 2 2 (Bx3-42 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·43⟩ c4) ▸
       at 3 2 (Toff403 ∷ Sw23 ∷ []) (lem-nat-2-TOFF402 c4) ▸
       at 4 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 5 2 (Bx3-42 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·43⟩ c4) ▸
       at 0 6 (Bx4-302 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;4103): 8 steps
lem-nat-2-BOX⟨2·4103⟩ : WsL → ⟪ (Sw23 ∷ Bx2-4103 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4102 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·4103⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-4103 ∷ []) (Bx3-4102 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff214 ∷ Bx4-203 ∷ Toff214 ∷ CCZ124 ∷ Bx4-203 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 1 2 (Toff314 ∷ Sw23 ∷ []) (lem-nat-2-TOFF214 c4) ▸
       at 2 2 (Bx4-302 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·203⟩ c4) ▸
       at 3 2 (Toff314 ∷ Sw23 ∷ []) (lem-nat-2-TOFF214 c4) ▸
       at 4 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 5 2 (Bx4-302 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·203⟩ c4) ▸
       at 0 6 (Bx3-4102 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;13): 3 steps
lem-nat-0-BOX⟨0·13⟩ : WsL → ⟪ (Sw01 ∷ Bx0-13 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-03 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·13⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-13 ∷ []) (Bx1-03 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ13 ∷ []) (refl) ▸
       at 0 2 (CZ03 ∷ Sw01 ∷ []) (sym (wl0088 c4)) ▸
       at 0 1 (Bx1-03 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;023): 8 steps
lem-nat-0-BOX⟨1·023⟩ : WsL → ⟪ (Sw01 ∷ Bx1-023 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-123 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·023⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-023 ∷ []) (Bx0-123 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 c4)) ▸
       at 1 2 (Toff012 ∷ Sw01 ∷ []) (wl0097 c4) ▸
       at 2 2 (Bx1-03 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·13⟩ c4) ▸
       at 3 2 (Toff012 ∷ Sw01 ∷ []) (wl0097 c4) ▸
       at 4 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 c4)) ▸
       at 5 2 (Bx1-03 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·13⟩ c4) ▸
       at 0 6 (Bx0-123 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;1423): 8 steps
lem-nat-0-BOX⟨0·1423⟩ : WsL → ⟪ (Sw01 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·1423⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-1423 ∷ []) (Bx1-0423 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff014 ∷ Bx1-023 ∷ Toff014 ∷ CCZ014 ∷ Bx1-023 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 1 2 (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 c4) ▸
       at 2 2 (Bx0-123 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·023⟩ c4) ▸
       at 3 2 (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 c4) ▸
       at 4 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 5 2 (Bx0-123 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·023⟩ c4) ▸
       at 0 6 (Bx1-0423 ∷ []) (refl) ▸ done


-- nat 1 BOX(1;03): 3 steps
lem-nat-1-BOX⟨1·03⟩ : WsL → ⟪ (Sw12 ∷ Bx1-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-03 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·03⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-03 ∷ []) (Bx2-03 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ03 ∷ []) (refl) ▸
       at 0 2 (CZ03 ∷ Sw12 ∷ []) (sym (wl0098 c4)) ▸
       at 0 1 (Bx2-03 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;123): 8 steps
lem-nat-1-BOX⟨0·123⟩ : WsL → ⟪ (Sw12 ∷ Bx0-123 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-213 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·123⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-123 ∷ []) (Bx0-213 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ Bx1-03 ∷ Toff012 ∷ CCZ012 ∷ Bx1-03 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 1 2 (Toff012 ∷ Sw12 ∷ []) (wl0038 c4) ▸
       at 2 2 (Bx2-03 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·03⟩ c4) ▸
       at 3 2 (Toff012 ∷ Sw12 ∷ []) (wl0038 c4) ▸
       at 4 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 5 2 (Bx2-03 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·03⟩ c4) ▸
       at 0 6 (Bx0-213 ∷ []) (refl) ▸ done


-- nat 1 BOX(1;0423): 8 steps
lem-nat-1-BOX⟨1·0423⟩ : WsL → ⟪ (Sw12 ∷ Bx1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·0423⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-0423 ∷ []) (Bx2-0413 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff104 ∷ Bx0-123 ∷ Toff104 ∷ CCZ014 ∷ Bx0-123 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 1 2 (Toff204 ∷ Sw12 ∷ []) (lem-nat-1-TOFF104 c4) ▸
       at 2 2 (Bx0-213 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·123⟩ c4) ▸
       at 3 2 (Toff204 ∷ Sw12 ∷ []) (lem-nat-1-TOFF104 c4) ▸
       at 4 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 5 2 (Bx0-213 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·123⟩ c4) ▸
       at 0 6 (Bx2-0413 ∷ []) (refl) ▸ done


-- nat 2 CZ03: 2 steps
lem-nat-2-CZ03 : WsL → ⟪ (Sw23 ∷ CZ03 ∷ []) ⟫ʷ ≈ ⟪ (CZ02 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-CZ03 c4 = run b0
  where
  b0 : Chain (Sw23 ∷ CZ03 ∷ []) (CZ02 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CZ02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0006 c4) ▸ done


-- nat 2 BOX(2;03): 3 steps
lem-nat-2-BOX⟨2·03⟩ : WsL → ⟪ (Sw23 ∷ Bx2-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-02 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·03⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-03 ∷ []) (Bx3-02 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ03 ∷ []) (refl) ▸
       at 0 2 (CZ02 ∷ Sw23 ∷ []) (lem-nat-2-CZ03 c4) ▸
       at 0 1 (Bx3-02 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;213): 8 steps
lem-nat-2-BOX⟨0·213⟩ : WsL → ⟪ (Sw23 ∷ Bx0-213 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-312 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·213⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-213 ∷ []) (Bx0-312 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 1 2 (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 c4) ▸
       at 2 2 (Bx3-02 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·03⟩ c4) ▸
       at 3 2 (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 c4) ▸
       at 4 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 5 2 (Bx3-02 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·03⟩ c4) ▸
       at 0 6 (Bx0-312 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;0413): 8 steps
lem-nat-2-BOX⟨2·0413⟩ : WsL → ⟪ (Sw23 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·0413⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-0413 ∷ []) (Bx3-0412 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 1 2 (Toff304 ∷ Sw23 ∷ []) (lem-nat-2-TOFF204 c4) ▸
       at 2 2 (Bx0-312 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·213⟩ c4) ▸
       at 3 2 (Toff304 ∷ Sw23 ∷ []) (lem-nat-2-TOFF204 c4) ▸
       at 4 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 5 2 (Bx0-312 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·213⟩ c4) ▸
       at 0 6 (Bx3-0412 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;03): 3 steps
lem-nat-0-BOX⟨1·03⟩ : WsL → ⟪ (Sw01 ∷ Bx1-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-13 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·03⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-03 ∷ []) (Bx0-13 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ03 ∷ []) (refl) ▸
       at 0 2 (CZ13 ∷ Sw01 ∷ []) (sym (wl0092 c4)) ▸
       at 0 1 (Bx0-13 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;123): 8 steps
lem-nat-0-BOX⟨0·123⟩ : WsL → ⟪ (Sw01 ∷ Bx0-123 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-023 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·123⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-123 ∷ []) (Bx1-023 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ Bx1-03 ∷ Toff012 ∷ CCZ012 ∷ Bx1-03 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 c4)) ▸
       at 1 2 (Toff102 ∷ Sw01 ∷ []) (wl0099 c4) ▸
       at 2 2 (Bx0-13 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·03⟩ c4) ▸
       at 3 2 (Toff102 ∷ Sw01 ∷ []) (wl0099 c4) ▸
       at 4 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 c4)) ▸
       at 5 2 (Bx0-13 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·03⟩ c4) ▸
       at 0 6 (Bx1-023 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;0423): 8 steps
lem-nat-0-BOX⟨1·0423⟩ : WsL → ⟪ (Sw01 ∷ Bx1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·0423⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-0423 ∷ []) (Bx0-1423 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff104 ∷ Bx0-123 ∷ Toff104 ∷ CCZ014 ∷ Bx0-123 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 1 2 (Toff014 ∷ Sw01 ∷ []) (lem-nat-0-TOFF104 c4) ▸
       at 2 2 (Bx1-023 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·123⟩ c4) ▸
       at 3 2 (Toff014 ∷ Sw01 ∷ []) (lem-nat-0-TOFF104 c4) ▸
       at 4 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 5 2 (Bx1-023 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·123⟩ c4) ▸
       at 0 6 (Bx0-1423 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;03): 3 steps
lem-nat-1-BOX⟨2·03⟩ : WsL → ⟪ (Sw12 ∷ Bx2-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-03 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·03⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-03 ∷ []) (Bx1-03 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ03 ∷ []) (refl) ▸
       at 0 2 (CZ03 ∷ Sw12 ∷ []) (sym (wl0098 c4)) ▸
       at 0 1 (Bx1-03 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;213): 8 steps
lem-nat-1-BOX⟨0·213⟩ : WsL → ⟪ (Sw12 ∷ Bx0-213 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-123 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·213⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-213 ∷ []) (Bx0-123 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 1 2 (Toff012 ∷ Sw12 ∷ []) (wl0038 c4) ▸
       at 2 2 (Bx1-03 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·03⟩ c4) ▸
       at 3 2 (Toff012 ∷ Sw12 ∷ []) (wl0038 c4) ▸
       at 4 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 5 2 (Bx1-03 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·03⟩ c4) ▸
       at 0 6 (Bx0-123 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;0413): 8 steps
lem-nat-1-BOX⟨2·0413⟩ : WsL → ⟪ (Sw12 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·0413⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-0413 ∷ []) (Bx1-0423 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 1 2 (Toff104 ∷ Sw12 ∷ []) (lem-nat-1-TOFF204 c4) ▸
       at 2 2 (Bx0-123 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·213⟩ c4) ▸
       at 3 2 (Toff104 ∷ Sw12 ∷ []) (lem-nat-1-TOFF204 c4) ▸
       at 4 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 5 2 (Bx0-123 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·213⟩ c4) ▸
       at 0 6 (Bx1-0423 ∷ []) (refl) ▸ done


-- nat 2 CZ02: 2 steps
lem-nat-2-CZ02 : WsL → ⟪ (Sw23 ∷ CZ02 ∷ []) ⟫ʷ ≈ ⟪ (CZ03 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-CZ02 c4 = run b0
  where
  b0 : Chain (Sw23 ∷ CZ02 ∷ []) (CZ03 ∷ Sw23 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 0 3 (CZ03 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 BOX(3;02): 3 steps
lem-nat-2-BOX⟨3·02⟩ : WsL → ⟪ (Sw23 ∷ Bx3-02 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-03 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·02⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-02 ∷ []) (Bx2-03 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ02 ∷ []) (refl) ▸
       at 0 2 (CZ03 ∷ Sw23 ∷ []) (lem-nat-2-CZ02 c4) ▸
       at 0 1 (Bx2-03 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;312): 8 steps
lem-nat-2-BOX⟨0·312⟩ : WsL → ⟪ (Sw23 ∷ Bx0-312 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-213 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·312⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-312 ∷ []) (Bx0-213 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff013 ∷ Bx3-02 ∷ Toff013 ∷ CCZ013 ∷ Bx3-02 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 1 2 (Toff012 ∷ Sw23 ∷ []) (lem-nat-2-TOFF013 c4) ▸
       at 2 2 (Bx2-03 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·02⟩ c4) ▸
       at 3 2 (Toff012 ∷ Sw23 ∷ []) (lem-nat-2-TOFF013 c4) ▸
       at 4 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 5 2 (Bx2-03 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·02⟩ c4) ▸
       at 0 6 (Bx0-213 ∷ []) (refl) ▸ done


-- nat 2 BOX(3;0412): 8 steps
lem-nat-2-BOX⟨3·0412⟩ : WsL → ⟪ (Sw23 ∷ Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·0412⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-0412 ∷ []) (Bx2-0413 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff304 ∷ Bx0-312 ∷ Toff304 ∷ CCZ034 ∷ Bx0-312 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 1 2 (Toff204 ∷ Sw23 ∷ []) (lem-nat-2-TOFF304 c4) ▸
       at 2 2 (Bx0-213 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·312⟩ c4) ▸
       at 3 2 (Toff204 ∷ Sw23 ∷ []) (lem-nat-2-TOFF304 c4) ▸
       at 4 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 5 2 (Bx0-213 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·312⟩ c4) ▸
       at 0 6 (Bx2-0413 ∷ []) (refl) ▸ done


-- resp CCZ014 at 2: 58 steps
lem-resp-CCZ014-at-2 : WsL → ⟪ (CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CCZ124 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CCZ014-at-2 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (CCZ014 ∷ []) (Sw12 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 1 3 (CCZ024 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 c4)) ▸
       at 1 1 (Sw12 ∷ CCZ014 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ CCZ013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw12 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b1 = at 5 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw12 ∷ Sw12 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw12 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b2 = at 8 2 [] (wl0006 c4) ▸
       at 4 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 2 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 4 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸ done

  b3 : Chain (Sw12 ∷ Sw12 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw12 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b3 = at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0007 c4) ▸
       at 1 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 c4)) ▸
       at 4 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 2 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS24⁻ ∷ Sw12 ∷ []) (sym (wl0009 c4)) ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (Sw12 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw12 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw01 ∷ Sw34 ∷ Sw01 ∷ Sw12 ∷ [])
  b4 = at 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 6 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸
       at 7 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 5 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0001 c4) ▸
       at 5 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸ done

  b5 : Chain (Sw12 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw01 ∷ Sw34 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ Sw34 ∷ Sw34 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Sw01 ∷ Sw12 ∷ [])
  b5 = at 6 2 (Sw01 ∷ CS13 ∷ []) (wl0019 c4) ▸
       at 5 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 6 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw01 ∷ CX12 ∷ []) (wl0048 c4) ▸
       at 3 2 (Sw01 ∷ CS24⁻ ∷ []) (sym (c₂ (Swap) (Swap ↑ • (CS • CS • CS) • Swap ↑))) ▸
       at 2 2 (Sw01 ∷ CX12 ∷ []) (wl0048 c4) ▸
       at 1 2 (Sw01 ∷ CS24 ∷ []) (sym (c₂ (Swap) (Swap ↑ • CS • Swap ↑))) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸ done

  b6 : Chain (Sw12 ∷ Sw01 ∷ Sw34 ∷ Sw34 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ Sw34 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw34 ∷ Sw01 ∷ Sw12 ∷ [])
  b6 = at 4 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0007 c4) ▸
       at 4 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 6 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0007 c4) ▸
       at 6 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 8 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0007 c4) ▸ done

  b7 : Chain (Sw12 ∷ Sw01 ∷ Sw34 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw34 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ CCZ124 ∷ Sw01 ∷ Sw12 ∷ [])
  b7 = at 3 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (CCZ124 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 BOX(4;203): 8 steps
lem-nat-0-BOX⟨4·203⟩ : WsL → ⟪ (Sw01 ∷ Bx4-203 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-213 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·203⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-203 ∷ []) (Bx4-213 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff402 ∷ Bx2-43 ∷ Toff402 ∷ CCZ024 ∷ Bx2-43 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 1 2 (Toff412 ∷ Sw01 ∷ []) (lem-nat-0-TOFF402 c4) ▸
       at 2 2 (Bx2-43 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸
       at 3 2 (Toff412 ∷ Sw01 ∷ []) (lem-nat-0-TOFF402 c4) ▸
       at 4 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 5 2 (Bx2-43 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸
       at 0 6 (Bx4-213 ∷ []) (refl) ▸ done


-- nat 0 BOX(2;4103): 8 steps
lem-nat-0-BOX⟨2·4103⟩ : WsL → ⟪ (Sw01 ∷ Bx2-4103 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·4103⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-4103 ∷ []) (Bx2-4013 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff214 ∷ Bx4-203 ∷ Toff214 ∷ CCZ124 ∷ Bx4-203 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 1 2 (Toff204 ∷ Sw01 ∷ []) (lem-nat-0-TOFF214 c4) ▸
       at 2 2 (Bx4-213 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·203⟩ c4) ▸
       at 3 2 (Toff204 ∷ Sw01 ∷ []) (lem-nat-0-TOFF214 c4) ▸
       at 4 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 5 2 (Bx4-213 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·203⟩ c4) ▸
       at 0 6 (Bx2-4013 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;04): 3 steps
lem-nat-0-BOX⟨1·04⟩ : WsL → ⟪ (Sw01 ∷ Bx1-04 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-14 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·04⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-04 ∷ []) (Bx0-14 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ04 ∷ []) (refl) ▸
       at 0 2 (CZ14 ∷ Sw01 ∷ []) (lem-nat-0-CZ04 c4) ▸
       at 0 1 (Bx0-14 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;134): 8 steps
lem-nat-0-BOX⟨0·134⟩ : WsL → ⟪ (Sw01 ∷ Bx0-134 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-034 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·134⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-134 ∷ []) (Bx1-034 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff013 ∷ Bx1-04 ∷ Toff013 ∷ CCZ013 ∷ Bx1-04 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw01 ∷ []) (sym (wl0100 c4)) ▸
       at 1 2 (Toff103 ∷ Sw01 ∷ []) (wl0101 c4) ▸
       at 2 2 (Bx0-14 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·04⟩ c4) ▸
       at 3 2 (Toff103 ∷ Sw01 ∷ []) (wl0101 c4) ▸
       at 4 2 (CCZ013 ∷ Sw01 ∷ []) (sym (wl0100 c4)) ▸
       at 5 2 (Bx0-14 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·04⟩ c4) ▸
       at 0 6 (Bx1-034 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;0234): 8 steps
lem-nat-0-BOX⟨1·0234⟩ : WsL → ⟪ (Sw01 ∷ Bx1-0234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·0234⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-0234 ∷ []) (Bx0-1234 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff102 ∷ Bx0-134 ∷ Toff102 ∷ CCZ012 ∷ Bx0-134 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 c4)) ▸
       at 1 2 (Toff012 ∷ Sw01 ∷ []) (wl0097 c4) ▸
       at 2 2 (Bx1-034 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·134⟩ c4) ▸
       at 3 2 (Toff012 ∷ Sw01 ∷ []) (wl0097 c4) ▸
       at 4 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 c4)) ▸
       at 5 2 (Bx1-034 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·134⟩ c4) ▸
       at 0 6 (Bx0-1234 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;043): 8 steps
lem-nat-0-BOX⟨1·043⟩ : WsL → ⟪ (Sw01 ∷ Bx1-043 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-143 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·043⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-043 ∷ []) (Bx0-143 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff104 ∷ Bx0-13 ∷ Toff104 ∷ CCZ014 ∷ Bx0-13 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 1 2 (Toff014 ∷ Sw01 ∷ []) (lem-nat-0-TOFF104 c4) ▸
       at 2 2 (Bx1-03 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·13⟩ c4) ▸
       at 3 2 (Toff014 ∷ Sw01 ∷ []) (lem-nat-0-TOFF104 c4) ▸
       at 4 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 5 2 (Bx1-03 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·13⟩ c4) ▸
       at 0 6 (Bx0-143 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;1243): 8 steps
lem-nat-0-BOX⟨0·1243⟩ : WsL → ⟪ (Sw01 ∷ Bx0-1243 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0243 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·1243⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-1243 ∷ []) (Bx1-0243 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ Bx1-043 ∷ Toff012 ∷ CCZ012 ∷ Bx1-043 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 c4)) ▸
       at 1 2 (Toff102 ∷ Sw01 ∷ []) (wl0099 c4) ▸
       at 2 2 (Bx0-143 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·043⟩ c4) ▸
       at 3 2 (Toff102 ∷ Sw01 ∷ []) (wl0099 c4) ▸
       at 4 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 c4)) ▸
       at 5 2 (Bx0-143 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·043⟩ c4) ▸
       at 0 6 (Bx1-0243 ∷ []) (refl) ▸ done


-- nat 1 TOFF023: 2 steps
lem-nat-1-TOFF023 : WsL → ⟪ (Sw12 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-TOFF023 c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Toff023 ∷ []) (Toff013 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Toff013 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0001 c4) ▸ done


-- nat 1 CZ04: 5 steps
lem-nat-1-CZ04 : WsL → ⟪ (Sw12 ∷ CZ04 ∷ []) ⟫ʷ ≈ ⟪ (CZ04 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-CZ04 c4 = run b0
  where
  b0 : Chain (Sw12 ∷ CZ04 ∷ []) (CZ04 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CZ03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 1 2 (CZ03 ∷ Sw12 ∷ []) (sym (wl0098 c4)) ▸
       at 2 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 0 3 (CZ04 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 1 BOX(2;04): 3 steps
lem-nat-1-BOX⟨2·04⟩ : WsL → ⟪ (Sw12 ∷ Bx2-04 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-04 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·04⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-04 ∷ []) (Bx1-04 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ04 ∷ []) (refl) ▸
       at 0 2 (CZ04 ∷ Sw12 ∷ []) (lem-nat-1-CZ04 c4) ▸
       at 0 1 (Bx1-04 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;234): 8 steps
lem-nat-1-BOX⟨0·234⟩ : WsL → ⟪ (Sw12 ∷ Bx0-234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-134 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·234⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-234 ∷ []) (Bx0-134 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff023 ∷ Bx2-04 ∷ Toff023 ∷ CCZ023 ∷ Bx2-04 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 1 2 (Toff013 ∷ Sw12 ∷ []) (lem-nat-1-TOFF023 c4) ▸
       at 2 2 (Bx1-04 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·04⟩ c4) ▸
       at 3 2 (Toff013 ∷ Sw12 ∷ []) (lem-nat-1-TOFF023 c4) ▸
       at 4 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 5 2 (Bx1-04 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·04⟩ c4) ▸
       at 0 6 (Bx0-134 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;0134): 8 steps
lem-nat-1-BOX⟨2·0134⟩ : WsL → ⟪ (Sw12 ∷ Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0234 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·0134⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-0134 ∷ []) (Bx1-0234 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff201 ∷ Bx0-234 ∷ Toff201 ∷ CCZ012 ∷ Bx0-234 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 1 2 (Toff102 ∷ Sw12 ∷ []) (wl0044 c4) ▸
       at 2 2 (Bx0-134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·234⟩ c4) ▸
       at 3 2 (Toff102 ∷ Sw12 ∷ []) (wl0044 c4) ▸
       at 4 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 5 2 (Bx0-134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·234⟩ c4) ▸
       at 0 6 (Bx1-0234 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;143): 8 steps
lem-nat-1-BOX⟨0·143⟩ : WsL → ⟪ (Sw12 ∷ Bx0-143 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-243 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·143⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-143 ∷ []) (Bx0-243 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff014 ∷ Bx1-03 ∷ Toff014 ∷ CCZ014 ∷ Bx1-03 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 1 2 (Toff024 ∷ Sw12 ∷ []) (lem-nat-1-TOFF014 c4) ▸
       at 2 2 (Bx2-03 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·03⟩ c4) ▸
       at 3 2 (Toff024 ∷ Sw12 ∷ []) (lem-nat-1-TOFF014 c4) ▸
       at 4 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 5 2 (Bx2-03 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·03⟩ c4) ▸
       at 0 6 (Bx0-243 ∷ []) (refl) ▸ done


-- nat 1 BOX(1;0243): 8 steps
lem-nat-1-BOX⟨1·0243⟩ : WsL → ⟪ (Sw12 ∷ Bx1-0243 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0143 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·0243⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-0243 ∷ []) (Bx2-0143 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff102 ∷ Bx0-143 ∷ Toff102 ∷ CCZ012 ∷ Bx0-143 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 1 2 (Toff201 ∷ Sw12 ∷ []) (wl0047 c4) ▸
       at 2 2 (Bx0-243 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·143⟩ c4) ▸
       at 3 2 (Toff201 ∷ Sw12 ∷ []) (wl0047 c4) ▸
       at 4 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 5 2 (Bx0-243 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·143⟩ c4) ▸
       at 0 6 (Bx2-0143 ∷ []) (refl) ▸ done


-- nat 2 CZ04: 7 steps
lem-nat-2-CZ04 : WsL → ⟪ (Sw23 ∷ CZ04 ∷ []) ⟫ʷ ≈ ⟪ (CZ04 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-CZ04 c4 = run b0
  where
  b0 : Chain (Sw23 ∷ CZ04 ∷ []) (CZ04 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0013 c4) ▸
       at 2 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 3 2 (CZ01 ∷ Sw34 ∷ []) (sym (c₂ (CZ) (Swap ↑))) ▸
       at 4 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 5 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (sym (wl0013 c4)) ▸
       at 0 7 (CZ04 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 BOX(3;04): 3 steps
lem-nat-2-BOX⟨3·04⟩ : WsL → ⟪ (Sw23 ∷ Bx3-04 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-04 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·04⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-04 ∷ []) (Bx2-04 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ04 ∷ []) (refl) ▸
       at 0 2 (CZ04 ∷ Sw23 ∷ []) (lem-nat-2-CZ04 c4) ▸
       at 0 1 (Bx2-04 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;324): 8 steps
lem-nat-2-BOX⟨0·324⟩ : WsL → ⟪ (Sw23 ∷ Bx0-324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-234 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·324⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-324 ∷ []) (Bx0-234 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw23 ∷ []) (sym (wl0065 c4)) ▸
       at 1 2 (Toff023 ∷ Sw23 ∷ []) (wl0093 c4) ▸
       at 2 2 (Bx2-04 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·04⟩ c4) ▸
       at 3 2 (Toff023 ∷ Sw23 ∷ []) (wl0093 c4) ▸
       at 4 2 (CCZ023 ∷ Sw23 ∷ []) (sym (wl0065 c4)) ▸
       at 5 2 (Bx2-04 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·04⟩ c4) ▸
       at 0 6 (Bx0-234 ∷ []) (refl) ▸ done


-- nat 2 BOX(3;0124): 8 steps
lem-nat-2-BOX⟨3·0124⟩ : WsL → ⟪ (Sw23 ∷ Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·0124⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-0124 ∷ []) (Bx2-0134 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff301 ∷ Bx0-324 ∷ Toff301 ∷ CCZ013 ∷ Bx0-324 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 1 2 (Toff201 ∷ Sw23 ∷ []) (lem-nat-2-TOFF301 c4) ▸
       at 2 2 (Bx0-234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·324⟩ c4) ▸
       at 3 2 (Toff201 ∷ Sw23 ∷ []) (lem-nat-2-TOFF301 c4) ▸
       at 4 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 5 2 (Bx0-234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·324⟩ c4) ▸
       at 0 6 (Bx2-0134 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;243): 8 steps
lem-nat-2-BOX⟨0·243⟩ : WsL → ⟪ (Sw23 ∷ Bx0-243 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-342 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·243⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-243 ∷ []) (Bx0-342 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx2-03 ∷ Toff024 ∷ CCZ024 ∷ Bx2-03 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 1 2 (Toff034 ∷ Sw23 ∷ []) (lem-nat-2-TOFF024 c4) ▸
       at 2 2 (Bx3-02 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·03⟩ c4) ▸
       at 3 2 (Toff034 ∷ Sw23 ∷ []) (lem-nat-2-TOFF024 c4) ▸
       at 4 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 5 2 (Bx3-02 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·03⟩ c4) ▸
       at 0 6 (Bx0-342 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;0143): 8 steps
lem-nat-2-BOX⟨2·0143⟩ : WsL → ⟪ (Sw23 ∷ Bx2-0143 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0142 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·0143⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-0143 ∷ []) (Bx3-0142 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff201 ∷ Bx0-243 ∷ Toff201 ∷ CCZ012 ∷ Bx0-243 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 1 2 (Toff301 ∷ Sw23 ∷ []) (lem-nat-2-TOFF201 c4) ▸
       at 2 2 (Bx0-342 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·243⟩ c4) ▸
       at 3 2 (Toff301 ∷ Sw23 ∷ []) (lem-nat-2-TOFF201 c4) ▸
       at 4 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 5 2 (Bx0-342 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·243⟩ c4) ▸
       at 0 6 (Bx3-0142 ∷ []) (refl) ▸ done


-- nat 3 CCZ123: 2 steps
lem-nat-3-CCZ123 : WsL → ⟪ (Sw34 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-CCZ123 c4 = run b0
  where
  b0 : Chain (Sw34 ∷ CCZ123 ∷ []) (CCZ124 ∷ Sw34 ∷ [])
  b0 = at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 0 3 (CCZ124 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 TOFF103: 2 steps
lem-nat-3-TOFF103 : WsL → ⟪ (Sw34 ∷ Toff103 ∷ []) ⟫ʷ ≈ ⟪ (Toff104 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-TOFF103 c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Toff103 ∷ []) (Toff104 ∷ Sw34 ∷ [])
  b0 = at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 0 3 (Toff104 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 BOX(1;034): 8 steps
lem-nat-3-BOX⟨1·034⟩ : WsL → ⟪ (Sw34 ∷ Bx1-034 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-043 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨1·034⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx1-034 ∷ []) (Bx1-043 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx0-14 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 1 2 (Toff104 ∷ Sw34 ∷ []) (lem-nat-3-TOFF103 c4) ▸
       at 2 2 (Bx0-13 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·14⟩ c4) ▸
       at 3 2 (Toff104 ∷ Sw34 ∷ []) (lem-nat-3-TOFF103 c4) ▸
       at 4 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 5 2 (Bx0-13 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·14⟩ c4) ▸
       at 0 6 (Bx1-043 ∷ []) (refl) ▸ done


-- nat 3 BOX(0;1234): 8 steps
lem-nat-3-BOX⟨0·1234⟩ : WsL → ⟪ (Sw34 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·1234⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx0-1234 ∷ []) (Bx0-1243 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ Bx1-034 ∷ Toff012 ∷ CCZ012 ∷ Bx1-034 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 1 2 (Toff012 ∷ Sw34 ∷ []) (sym (c₃ (Toff) (Swap))) ▸
       at 2 2 (Bx1-043 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·034⟩ c4) ▸
       at 3 2 (Toff012 ∷ Sw34 ∷ []) (sym (c₃ (Toff) (Swap))) ▸
       at 4 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 5 2 (Bx1-043 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·034⟩ c4) ▸
       at 0 6 (Bx0-1243 ∷ []) (refl) ▸ done


-- nat 3 CCZ124: 2 steps
lem-nat-3-CCZ124 : WsL → ⟪ (Sw34 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-CCZ124 c4 = run b0
  where
  b0 : Chain (Sw34 ∷ CCZ124 ∷ []) (CCZ123 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0007 c4) ▸ done


-- nat 0 BOX(0;143): 8 steps
lem-nat-0-BOX⟨0·143⟩ : WsL → ⟪ (Sw01 ∷ Bx0-143 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-043 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·143⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-143 ∷ []) (Bx1-043 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff014 ∷ Bx1-03 ∷ Toff014 ∷ CCZ014 ∷ Bx1-03 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 1 2 (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 c4) ▸
       at 2 2 (Bx0-13 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·03⟩ c4) ▸
       at 3 2 (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 c4) ▸
       at 4 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 5 2 (Bx0-13 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·03⟩ c4) ▸
       at 0 6 (Bx1-043 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;0243): 8 steps
lem-nat-0-BOX⟨1·0243⟩ : WsL → ⟪ (Sw01 ∷ Bx1-0243 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·0243⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-0243 ∷ []) (Bx0-1243 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff102 ∷ Bx0-143 ∷ Toff102 ∷ CCZ012 ∷ Bx0-143 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 c4)) ▸
       at 1 2 (Toff012 ∷ Sw01 ∷ []) (wl0097 c4) ▸
       at 2 2 (Bx1-043 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·143⟩ c4) ▸
       at 3 2 (Toff012 ∷ Sw01 ∷ []) (wl0097 c4) ▸
       at 4 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 c4)) ▸
       at 5 2 (Bx1-043 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·143⟩ c4) ▸
       at 0 6 (Bx0-1243 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;243): 8 steps
lem-nat-1-BOX⟨0·243⟩ : WsL → ⟪ (Sw12 ∷ Bx0-243 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-143 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·243⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-243 ∷ []) (Bx0-143 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx2-03 ∷ Toff024 ∷ CCZ024 ∷ Bx2-03 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 1 2 (Toff014 ∷ Sw12 ∷ []) (lem-nat-1-TOFF024 c4) ▸
       at 2 2 (Bx1-03 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·03⟩ c4) ▸
       at 3 2 (Toff014 ∷ Sw12 ∷ []) (lem-nat-1-TOFF024 c4) ▸
       at 4 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 5 2 (Bx1-03 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·03⟩ c4) ▸
       at 0 6 (Bx0-143 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;0143): 8 steps
lem-nat-1-BOX⟨2·0143⟩ : WsL → ⟪ (Sw12 ∷ Bx2-0143 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0243 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·0143⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-0143 ∷ []) (Bx1-0243 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff201 ∷ Bx0-243 ∷ Toff201 ∷ CCZ012 ∷ Bx0-243 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 1 2 (Toff102 ∷ Sw12 ∷ []) (wl0044 c4) ▸
       at 2 2 (Bx0-143 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·243⟩ c4) ▸
       at 3 2 (Toff102 ∷ Sw12 ∷ []) (wl0044 c4) ▸
       at 4 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 5 2 (Bx0-143 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·243⟩ c4) ▸
       at 0 6 (Bx1-0243 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;342): 8 steps
lem-nat-2-BOX⟨0·342⟩ : WsL → ⟪ (Sw23 ∷ Bx0-342 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-243 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·342⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-342 ∷ []) (Bx0-243 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff034 ∷ Bx3-02 ∷ Toff034 ∷ CCZ034 ∷ Bx3-02 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 1 2 (Toff024 ∷ Sw23 ∷ []) (lem-nat-2-TOFF034 c4) ▸
       at 2 2 (Bx2-03 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·02⟩ c4) ▸
       at 3 2 (Toff024 ∷ Sw23 ∷ []) (lem-nat-2-TOFF034 c4) ▸
       at 4 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 5 2 (Bx2-03 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·02⟩ c4) ▸
       at 0 6 (Bx0-243 ∷ []) (refl) ▸ done


-- nat 2 BOX(3;0142): 8 steps
lem-nat-2-BOX⟨3·0142⟩ : WsL → ⟪ (Sw23 ∷ Bx3-0142 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0143 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·0142⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-0142 ∷ []) (Bx2-0143 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff301 ∷ Bx0-342 ∷ Toff301 ∷ CCZ013 ∷ Bx0-342 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 1 2 (Toff201 ∷ Sw23 ∷ []) (lem-nat-2-TOFF301 c4) ▸
       at 2 2 (Bx0-243 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·342⟩ c4) ▸
       at 3 2 (Toff201 ∷ Sw23 ∷ []) (lem-nat-2-TOFF301 c4) ▸
       at 4 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 5 2 (Bx0-243 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·342⟩ c4) ▸
       at 0 6 (Bx2-0143 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;14): 3 steps
lem-nat-0-BOX⟨0·14⟩ : WsL → ⟪ (Sw01 ∷ Bx0-14 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-04 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·14⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-14 ∷ []) (Bx1-04 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ14 ∷ []) (refl) ▸
       at 0 2 (CZ04 ∷ Sw01 ∷ []) (lem-nat-0-CZ14 c4) ▸
       at 0 1 (Bx1-04 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;034): 8 steps
lem-nat-0-BOX⟨1·034⟩ : WsL → ⟪ (Sw01 ∷ Bx1-034 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-134 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·034⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-034 ∷ []) (Bx0-134 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx0-14 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw01 ∷ []) (sym (wl0100 c4)) ▸
       at 1 2 (Toff013 ∷ Sw01 ∷ []) (wl0102 c4) ▸
       at 2 2 (Bx1-04 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·14⟩ c4) ▸
       at 3 2 (Toff013 ∷ Sw01 ∷ []) (wl0102 c4) ▸
       at 4 2 (CCZ013 ∷ Sw01 ∷ []) (sym (wl0100 c4)) ▸
       at 5 2 (Bx1-04 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·14⟩ c4) ▸
       at 0 6 (Bx0-134 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;1234): 8 steps
lem-nat-0-BOX⟨0·1234⟩ : WsL → ⟪ (Sw01 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0234 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·1234⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-1234 ∷ []) (Bx1-0234 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ Bx1-034 ∷ Toff012 ∷ CCZ012 ∷ Bx1-034 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 c4)) ▸
       at 1 2 (Toff102 ∷ Sw01 ∷ []) (wl0099 c4) ▸
       at 2 2 (Bx0-134 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·034⟩ c4) ▸
       at 3 2 (Toff102 ∷ Sw01 ∷ []) (wl0099 c4) ▸
       at 4 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 c4)) ▸
       at 5 2 (Bx0-134 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·034⟩ c4) ▸
       at 0 6 (Bx1-0234 ∷ []) (refl) ▸ done


-- nat 1 BOX(1;04): 3 steps
lem-nat-1-BOX⟨1·04⟩ : WsL → ⟪ (Sw12 ∷ Bx1-04 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-04 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·04⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-04 ∷ []) (Bx2-04 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ04 ∷ []) (refl) ▸
       at 0 2 (CZ04 ∷ Sw12 ∷ []) (lem-nat-1-CZ04 c4) ▸
       at 0 1 (Bx2-04 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;134): 8 steps
lem-nat-1-BOX⟨0·134⟩ : WsL → ⟪ (Sw12 ∷ Bx0-134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-234 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·134⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-134 ∷ []) (Bx0-234 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff013 ∷ Bx1-04 ∷ Toff013 ∷ CCZ013 ∷ Bx1-04 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 1 2 (Toff023 ∷ Sw12 ∷ []) (lem-nat-1-TOFF013 c4) ▸
       at 2 2 (Bx2-04 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·04⟩ c4) ▸
       at 3 2 (Toff023 ∷ Sw12 ∷ []) (lem-nat-1-TOFF013 c4) ▸
       at 4 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 5 2 (Bx2-04 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·04⟩ c4) ▸
       at 0 6 (Bx0-234 ∷ []) (refl) ▸ done


-- nat 1 BOX(1;0234): 8 steps
lem-nat-1-BOX⟨1·0234⟩ : WsL → ⟪ (Sw12 ∷ Bx1-0234 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·0234⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-0234 ∷ []) (Bx2-0134 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff102 ∷ Bx0-134 ∷ Toff102 ∷ CCZ012 ∷ Bx0-134 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 1 2 (Toff201 ∷ Sw12 ∷ []) (wl0047 c4) ▸
       at 2 2 (Bx0-234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·134⟩ c4) ▸
       at 3 2 (Toff201 ∷ Sw12 ∷ []) (wl0047 c4) ▸
       at 4 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 5 2 (Bx0-234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·134⟩ c4) ▸
       at 0 6 (Bx2-0134 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;04): 3 steps
lem-nat-2-BOX⟨2·04⟩ : WsL → ⟪ (Sw23 ∷ Bx2-04 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-04 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·04⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-04 ∷ []) (Bx3-04 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ04 ∷ []) (refl) ▸
       at 0 2 (CZ04 ∷ Sw23 ∷ []) (lem-nat-2-CZ04 c4) ▸
       at 0 1 (Bx3-04 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;234): 8 steps
lem-nat-2-BOX⟨0·234⟩ : WsL → ⟪ (Sw23 ∷ Bx0-234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-324 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·234⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-234 ∷ []) (Bx0-324 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff023 ∷ Bx2-04 ∷ Toff023 ∷ CCZ023 ∷ Bx2-04 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw23 ∷ []) (sym (wl0065 c4)) ▸
       at 1 2 (Toff023 ∷ Sw23 ∷ []) (wl0093 c4) ▸
       at 2 2 (Bx3-04 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·04⟩ c4) ▸
       at 3 2 (Toff023 ∷ Sw23 ∷ []) (wl0093 c4) ▸
       at 4 2 (CCZ023 ∷ Sw23 ∷ []) (sym (wl0065 c4)) ▸
       at 5 2 (Bx3-04 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·04⟩ c4) ▸
       at 0 6 (Bx0-324 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;0134): 8 steps
lem-nat-2-BOX⟨2·0134⟩ : WsL → ⟪ (Sw23 ∷ Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·0134⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-0134 ∷ []) (Bx3-0124 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff201 ∷ Bx0-234 ∷ Toff201 ∷ CCZ012 ∷ Bx0-234 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 1 2 (Toff301 ∷ Sw23 ∷ []) (lem-nat-2-TOFF201 c4) ▸
       at 2 2 (Bx0-324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·234⟩ c4) ▸
       at 3 2 (Toff301 ∷ Sw23 ∷ []) (lem-nat-2-TOFF201 c4) ▸
       at 4 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 5 2 (Bx0-324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·234⟩ c4) ▸
       at 0 6 (Bx3-0124 ∷ []) (refl) ▸ done


-- resp TOFF314 at 2: 4 steps
lem-resp-TOFF314-at-2 : WsL → ⟪ (Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ Toff324 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-TOFF314-at-2 c4 = run b0
  where
  b0 : Chain (Toff314 ∷ []) (Sw12 ∷ Sw01 ∷ Toff324 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 0 2 (Sw12 ∷ Toff324 ∷ []) (sym (wl0063 c4)) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 c4)) ▸
       at 1 2 (Sw01 ∷ Toff324 ∷ []) (sym (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI))) ▸ done


-- resp CS03 at 2: 4 steps
lem-resp-CS03-at-2 : WsL → ⟪ (CS03 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CS13 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CS03-at-2 c4 = run b0
  where
  b0 : Chain (CS03 ∷ []) (Sw12 ∷ Sw01 ∷ CS13 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 0 2 (Sw12 ∷ CS03 ∷ []) (wl0010 c4) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 c4)) ▸
       at 1 2 (Sw01 ∷ CS13 ∷ []) (wl0019 c4) ▸ done


-- resp CSd03 at 2: 4 steps
lem-resp-CSd03-at-2 : WsL → ⟪ (CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CS13⁻ ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CSd03-at-2 c4 = run b0
  where
  b0 : Chain (CS03⁻ ∷ []) (Sw12 ∷ Sw01 ∷ CS13⁻ ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 0 2 (Sw12 ∷ CS03⁻ ∷ []) (wl0023 c4) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 c4)) ▸
       at 1 2 (Sw01 ∷ CS13⁻ ∷ []) (wl0022 c4) ▸ done


-- nat 1 BOX(3;04): 3 steps
lem-nat-1-BOX⟨3·04⟩ : WsL → ⟪ (Sw12 ∷ Bx3-04 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-04 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·04⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-04 ∷ []) (Bx3-04 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ04 ∷ []) (refl) ▸
       at 0 2 (CZ04 ∷ Sw12 ∷ []) (lem-nat-1-CZ04 c4) ▸
       at 0 1 (Bx3-04 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;314): 8 steps
lem-nat-1-BOX⟨0·314⟩ : WsL → ⟪ (Sw12 ∷ Bx0-314 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-324 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·314⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-314 ∷ []) (Bx0-324 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff013 ∷ Bx3-04 ∷ Toff013 ∷ CCZ013 ∷ Bx3-04 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 1 2 (Toff023 ∷ Sw12 ∷ []) (lem-nat-1-TOFF013 c4) ▸
       at 2 2 (Bx3-04 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·04⟩ c4) ▸
       at 3 2 (Toff023 ∷ Sw12 ∷ []) (lem-nat-1-TOFF013 c4) ▸
       at 4 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 5 2 (Bx3-04 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·04⟩ c4) ▸
       at 0 6 (Bx0-324 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;0214): 8 steps
lem-nat-1-BOX⟨3·0214⟩ : WsL → ⟪ (Sw12 ∷ Bx3-0214 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·0214⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-0214 ∷ []) (Bx3-0124 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff302 ∷ Bx0-314 ∷ Toff302 ∷ CCZ023 ∷ Bx0-314 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 1 2 (Toff301 ∷ Sw12 ∷ []) (lem-nat-1-TOFF302 c4) ▸
       at 2 2 (Bx0-324 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·314⟩ c4) ▸
       at 3 2 (Toff301 ∷ Sw12 ∷ []) (lem-nat-1-TOFF302 c4) ▸
       at 4 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 5 2 (Bx0-324 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·314⟩ c4) ▸
       at 0 6 (Bx3-0124 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;324): 8 steps
lem-nat-1-BOX⟨0·324⟩ : WsL → ⟪ (Sw12 ∷ Bx0-324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-314 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·324⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-324 ∷ []) (Bx0-314 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 1 2 (Toff013 ∷ Sw12 ∷ []) (lem-nat-1-TOFF023 c4) ▸
       at 2 2 (Bx3-04 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·04⟩ c4) ▸
       at 3 2 (Toff013 ∷ Sw12 ∷ []) (lem-nat-1-TOFF023 c4) ▸
       at 4 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 5 2 (Bx3-04 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·04⟩ c4) ▸
       at 0 6 (Bx0-314 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;0124): 8 steps
lem-nat-1-BOX⟨3·0124⟩ : WsL → ⟪ (Sw12 ∷ Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0214 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·0124⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-0124 ∷ []) (Bx3-0214 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff301 ∷ Bx0-324 ∷ Toff301 ∷ CCZ013 ∷ Bx0-324 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 1 2 (Toff302 ∷ Sw12 ∷ []) (lem-nat-1-TOFF301 c4) ▸
       at 2 2 (Bx0-314 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·324⟩ c4) ▸
       at 3 2 (Toff302 ∷ Sw12 ∷ []) (lem-nat-1-TOFF301 c4) ▸
       at 4 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 5 2 (Bx0-314 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·324⟩ c4) ▸
       at 0 6 (Bx3-0214 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;214): 8 steps
lem-nat-2-BOX⟨0·214⟩ : WsL → ⟪ (Sw23 ∷ Bx0-214 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-314 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·214⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-214 ∷ []) (Bx0-314 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ Bx2-04 ∷ Toff012 ∷ CCZ012 ∷ Bx2-04 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 1 2 (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 c4) ▸
       at 2 2 (Bx3-04 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·04⟩ c4) ▸
       at 3 2 (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 c4) ▸
       at 4 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 5 2 (Bx3-04 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·04⟩ c4) ▸
       at 0 6 (Bx0-314 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;0314): 8 steps
lem-nat-2-BOX⟨2·0314⟩ : WsL → ⟪ (Sw23 ∷ Bx2-0314 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0214 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·0314⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-0314 ∷ []) (Bx3-0214 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff203 ∷ Bx0-214 ∷ Toff203 ∷ CCZ023 ∷ Bx0-214 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw23 ∷ []) (sym (wl0065 c4)) ▸
       at 1 2 (Toff302 ∷ Sw23 ∷ []) (wl0090 c4) ▸
       at 2 2 (Bx0-314 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·214⟩ c4) ▸
       at 3 2 (Toff302 ∷ Sw23 ∷ []) (wl0090 c4) ▸
       at 4 2 (CCZ023 ∷ Sw23 ∷ []) (sym (wl0065 c4)) ▸
       at 5 2 (Bx0-314 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·214⟩ c4) ▸
       at 0 6 (Bx3-0214 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;314): 8 steps
lem-nat-2-BOX⟨0·314⟩ : WsL → ⟪ (Sw23 ∷ Bx0-314 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-214 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·314⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-314 ∷ []) (Bx0-214 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff013 ∷ Bx3-04 ∷ Toff013 ∷ CCZ013 ∷ Bx3-04 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 1 2 (Toff012 ∷ Sw23 ∷ []) (lem-nat-2-TOFF013 c4) ▸
       at 2 2 (Bx2-04 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·04⟩ c4) ▸
       at 3 2 (Toff012 ∷ Sw23 ∷ []) (lem-nat-2-TOFF013 c4) ▸
       at 4 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 5 2 (Bx2-04 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·04⟩ c4) ▸
       at 0 6 (Bx0-214 ∷ []) (refl) ▸ done


-- nat 2 BOX(3;0214): 8 steps
lem-nat-2-BOX⟨3·0214⟩ : WsL → ⟪ (Sw23 ∷ Bx3-0214 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0314 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·0214⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-0214 ∷ []) (Bx2-0314 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff302 ∷ Bx0-314 ∷ Toff302 ∷ CCZ023 ∷ Bx0-314 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw23 ∷ []) (sym (wl0065 c4)) ▸
       at 1 2 (Toff203 ∷ Sw23 ∷ []) (wl0066 c4) ▸
       at 2 2 (Bx0-214 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·314⟩ c4) ▸
       at 3 2 (Toff203 ∷ Sw23 ∷ []) (wl0066 c4) ▸
       at 4 2 (CCZ023 ∷ Sw23 ∷ []) (sym (wl0065 c4)) ▸
       at 5 2 (Bx0-214 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·314⟩ c4) ▸
       at 0 6 (Bx2-0314 ∷ []) (refl) ▸ done


-- nat 3 CZ03: 2 steps
lem-nat-3-CZ03 : WsL → ⟪ (Sw34 ∷ CZ03 ∷ []) ⟫ʷ ≈ ⟪ (CZ04 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-CZ03 c4 = run b0
  where
  b0 : Chain (Sw34 ∷ CZ03 ∷ []) (CZ04 ∷ Sw34 ∷ [])
  b0 = at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 0 3 (CZ04 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 BOX(2;03): 3 steps
lem-nat-3-BOX⟨2·03⟩ : WsL → ⟪ (Sw34 ∷ Bx2-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-04 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·03⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx2-03 ∷ []) (Bx2-04 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ03 ∷ []) (refl) ▸
       at 0 2 (CZ04 ∷ Sw34 ∷ []) (lem-nat-3-CZ03 c4) ▸
       at 0 1 (Bx2-04 ∷ []) (refl) ▸ done


-- nat 3 BOX(0;213): 8 steps
lem-nat-3-BOX⟨0·213⟩ : WsL → ⟪ (Sw34 ∷ Bx0-213 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-214 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·213⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx0-213 ∷ []) (Bx0-214 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 1 2 (Toff012 ∷ Sw34 ∷ []) (sym (c₃ (Toff) (Swap))) ▸
       at 2 2 (Bx2-04 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·03⟩ c4) ▸
       at 3 2 (Toff012 ∷ Sw34 ∷ []) (sym (c₃ (Toff) (Swap))) ▸
       at 4 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 5 2 (Bx2-04 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·03⟩ c4) ▸
       at 0 6 (Bx0-214 ∷ []) (refl) ▸ done


-- nat 3 BOX(2;0413): 8 steps
lem-nat-3-BOX⟨2·0413⟩ : WsL → ⟪ (Sw34 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0314 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·0413⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx2-0413 ∷ []) (Bx2-0314 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 1 2 (Toff203 ∷ Sw34 ∷ []) (lem-nat-3-TOFF204 c4) ▸
       at 2 2 (Bx0-214 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·213⟩ c4) ▸
       at 3 2 (Toff203 ∷ Sw34 ∷ []) (lem-nat-3-TOFF204 c4) ▸
       at 4 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 5 2 (Bx0-214 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·213⟩ c4) ▸
       at 0 6 (Bx2-0314 ∷ []) (refl) ▸ done


-- nat 3 CZ04: 2 steps
lem-nat-3-CZ04 : WsL → ⟪ (Sw34 ∷ CZ04 ∷ []) ⟫ʷ ≈ ⟪ (CZ03 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-CZ04 c4 = run b0
  where
  b0 : Chain (Sw34 ∷ CZ04 ∷ []) (CZ03 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CZ03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0007 c4) ▸ done


-- nat 3 BOX(2;04): 3 steps
lem-nat-3-BOX⟨2·04⟩ : WsL → ⟪ (Sw34 ∷ Bx2-04 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-03 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·04⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx2-04 ∷ []) (Bx2-03 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ04 ∷ []) (refl) ▸
       at 0 2 (CZ03 ∷ Sw34 ∷ []) (lem-nat-3-CZ04 c4) ▸
       at 0 1 (Bx2-03 ∷ []) (refl) ▸ done


-- nat 3 BOX(0;214): 8 steps
lem-nat-3-BOX⟨0·214⟩ : WsL → ⟪ (Sw34 ∷ Bx0-214 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-213 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·214⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx0-214 ∷ []) (Bx0-213 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ Bx2-04 ∷ Toff012 ∷ CCZ012 ∷ Bx2-04 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 1 2 (Toff012 ∷ Sw34 ∷ []) (sym (c₃ (Toff) (Swap))) ▸
       at 2 2 (Bx2-03 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·04⟩ c4) ▸
       at 3 2 (Toff012 ∷ Sw34 ∷ []) (sym (c₃ (Toff) (Swap))) ▸
       at 4 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 5 2 (Bx2-03 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·04⟩ c4) ▸
       at 0 6 (Bx0-213 ∷ []) (refl) ▸ done


-- nat 3 BOX(2;0314): 8 steps
lem-nat-3-BOX⟨2·0314⟩ : WsL → ⟪ (Sw34 ∷ Bx2-0314 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·0314⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx2-0314 ∷ []) (Bx2-0413 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff203 ∷ Bx0-214 ∷ Toff203 ∷ CCZ023 ∷ Bx0-214 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4) ▸
       at 1 2 (Toff204 ∷ Sw34 ∷ []) (lem-nat-3-TOFF203 c4) ▸
       at 2 2 (Bx0-213 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·214⟩ c4) ▸
       at 3 2 (Toff204 ∷ Sw34 ∷ []) (lem-nat-3-TOFF203 c4) ▸
       at 4 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4) ▸
       at 5 2 (Bx0-213 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·214⟩ c4) ▸
       at 0 6 (Bx2-0413 ∷ []) (refl) ▸ done


-- nat 2 CCZ014: 53 steps
lem-nat-2-CCZ014 : WsL → ⟪ (Sw23 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-CCZ014 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (run b6))))))
  where
  b0 : Chain (Sw23 ∷ CCZ014 ∷ []) (Sw23 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CCZ013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 4 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ CS14 ∷ CX01 ∷ Sw34 ∷ CS13⁻ ∷ Sw34 ∷ Sw34 ∷ CX01 ∷ CS03 ∷ Sw34 ∷ [])
  b1 = at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0006 c4) ▸
       at 3 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 1 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸ done

  b2 : Chain (Sw23 ∷ CS14 ∷ CX01 ∷ Sw34 ∷ CS13⁻ ∷ Sw34 ∷ Sw34 ∷ CX01 ∷ CS03 ∷ Sw34 ∷ []) (CS14 ∷ CX01 ∷ CS14⁻ ∷ Sw23 ∷ CX01 ∷ CS04 ∷ [])
  b2 = at 3 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 5 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0007 c4) ▸
       at 0 2 (CS14 ∷ Sw23 ∷ []) (sym (wl0021 c4)) ▸
       at 1 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 2 2 (CS14⁻ ∷ Sw23 ∷ []) (sym (wl0033 c4)) ▸ done

  b3 : Chain (CS14 ∷ CX01 ∷ CS14⁻ ∷ Sw23 ∷ CX01 ∷ CS04 ∷ []) (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw23 ∷ [])
  b3 = at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 5 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0013 c4) ▸
       at 6 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 7 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 8 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 9 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (sym (wl0013 c4)) ▸
       at 4 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw23 ∷ []) (Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw34 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw23 ∷ [])
  b4 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 2 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0007 c4) ▸
       at 2 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 4 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0007 c4) ▸
       at 4 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b5 : Chain (Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw34 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ CS03 ∷ Sw34 ∷ Sw23 ∷ [])
  b5 = at 5 2 [] (wl0007 c4) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0006 c4) ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0006 c4) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸ done

  b6 : Chain (Sw34 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ CS03 ∷ Sw34 ∷ Sw23 ∷ []) (CCZ014 ∷ Sw23 ∷ [])
  b6 = at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0006 c4) ▸
       at 2 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (CCZ014 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CCZ014 at 3: 112 steps
lem-resp-CCZ014-at-3 : WsL → ⟪ (CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CCZ124 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CCZ014-at-3 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (run b13)))))))))))))
  where
  b0 : Chain (CCZ014 ∷ []) (Sw34 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw34 ∷ Sw23 ∷ Sw23 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 0 1 (Sw34 ∷ CCZ013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 1 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸ done

  b1 : Chain (Sw34 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw34 ∷ Sw23 ∷ Sw23 ∷ []) (CS14 ∷ CX01 ∷ Sw34 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw34 ∷ Sw23 ∷ Sw23 ∷ [])
  b1 = at 3 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0006 c4) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 0 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸ done

  b2 : Chain (CS14 ∷ CX01 ∷ Sw34 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw34 ∷ Sw23 ∷ Sw23 ∷ []) (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ Sw23 ∷ [])
  b2 = at 4 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 2 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 4 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0007 c4) ▸
       at 4 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 9 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0013 c4) ▸ done

  b3 : Chain (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (CS14 ∷ Sw23 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw23 ∷ [])
  b3 = at 8 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 7 2 (Sw34 ∷ CS01 ∷ []) (c₂ (CS) (Swap ↑)) ▸
       at 6 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 4 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (sym (wl0013 c4)) ▸
       at 5 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw23 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Swap)) ▸
       at 2 2 (Sw23 ∷ CS14⁻ ∷ []) (wl0033 c4) ▸
       at 1 2 (Sw23 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Swap)) ▸ done

  b4 : Chain (CS14 ∷ Sw23 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw23 ∷ []) (Sw23 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw34 ∷ CS04 ∷ Sw23 ∷ [])
  b4 = at 0 2 (Sw23 ∷ CS14 ∷ []) (wl0021 c4) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 3 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0007 c4) ▸
       at 3 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 5 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0007 c4) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸ done

  b5 : Chain (Sw23 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw34 ∷ CS04 ∷ Sw23 ∷ []) (Sw23 ∷ Sw34 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ Sw34 ∷ Sw23 ∷ [])
  b5 = at 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0007 c4) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0006 c4) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0006 c4) ▸ done

  b6 : Chain (Sw23 ∷ Sw34 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ Sw34 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw12 ∷ CCZ014 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ [])
  b6 = at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0006 c4) ▸
       at 3 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (CCZ014 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸ done

  b7 : Chain (Sw23 ∷ Sw12 ∷ Sw12 ∷ CCZ014 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw34 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b7 = at 2 3 (CCZ024 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 c4)) ▸
       at 2 1 (Sw12 ∷ CCZ014 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ CCZ013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b8 : Chain (Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw34 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ Sw34 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b8 = at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (wl0006 c4) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸ done

  b9 : Chain (Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ Sw34 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw12 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b9 = at 3 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 5 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 9 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 7 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0007 c4) ▸ done

  b10 : Chain (Sw23 ∷ Sw12 ∷ Sw12 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ Sw12 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b10 = at 2 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 c4)) ▸
       at 5 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 3 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS24⁻ ∷ Sw12 ∷ []) (sym (wl0009 c4)) ▸
       at 7 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 5 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸ done

  b11 : Chain (Sw23 ∷ Sw12 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ Sw12 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw01 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b11 = at 7 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸
       at 8 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0001 c4) ▸
       at 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 7 2 (Sw01 ∷ CS13 ∷ []) (wl0019 c4) ▸
       at 6 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸ done

  b12 : Chain (Sw23 ∷ Sw12 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw01 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ Sw34 ∷ CS23 ∷ Sw34 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b12 = at 7 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw01 ∷ CX12 ∷ []) (wl0048 c4) ▸
       at 4 2 (Sw01 ∷ CS24⁻ ∷ []) (sym (c₂ (Swap) (Swap ↑ • (CS • CS • CS) • Swap ↑))) ▸
       at 3 2 (Sw01 ∷ CX12 ∷ []) (wl0048 c4) ▸
       at 2 2 (Sw01 ∷ CS24 ∷ []) (sym (c₂ (Swap) (Swap ↑ • CS • Swap ↑))) ▸
       at 3 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 5 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0007 c4) ▸ done

  b13 : Chain (Sw23 ∷ Sw12 ∷ Sw01 ∷ Sw34 ∷ CS23 ∷ Sw34 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CCZ124 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b13 = at 5 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 7 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0007 c4) ▸
       at 7 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 9 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0007 c4) ▸
       at 4 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (CCZ124 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp TOFF214 at 3: 7 steps
lem-resp-TOFF214-at-3 : WsL → ⟪ (Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff324 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-TOFF214-at-3 c4 = run b0
  where
  b0 : Chain (Toff214 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff324 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 1 3 (Toff314 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 1 2 (Sw12 ∷ Toff324 ∷ []) (sym (wl0063 c4)) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 c4)) ▸
       at 2 2 (Sw01 ∷ Toff324 ∷ []) (sym (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI))) ▸ done


-- resp TOFF204 at 1: 71 steps
lem-resp-TOFF204-at-1 : WsL → ⟪ (Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Toff214 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-TOFF204-at-1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (run b8))))))))
  where
  b0 : Chain (Toff204 ∷ []) (Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 c4)) ▸
       at 0 1 (Sw12 ∷ Toff104 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw34 ∷ Toff103 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ []) (Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ [])
  b1 = at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸ done

  b2 : Chain (Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ []) (Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ [])
  b2 = at 10 2 [] (wl0006 c4) ▸
       at 1 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 4 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 2 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 4 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸ done

  b3 : Chain (Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ []) (K2 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ [])
  b3 = at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 8 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 9 2 [] (wl0007 c4) ▸
       at 0 2 (K2 ∷ Sw12 ∷ []) (sym (wl0056 c4)) ▸
       at 1 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 c4)) ▸
       at 4 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸ done

  b4 : Chain (K2 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ []) (K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ [])
  b4 = at 2 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS24⁻ ∷ Sw12 ∷ []) (sym (wl0009 c4)) ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 6 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸
       at 7 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸ done

  b5 : Chain (K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ []) (K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw01 ∷ Sw34 ∷ K2 ∷ ι ∷ Sw01 ∷ [])
  b5 = at 5 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K2 ∷ Sw12 ∷ []) (sym (wl0056 c4)) ▸
       at 7 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 8 2 [] (wl0001 c4) ▸
       at 7 2 (Sw01 ∷ ι ∷ []) (sym (wl0030 c4)) ▸
       at 6 2 (Sw01 ∷ K2 ∷ []) (sym (c₂ (Swap) (K))) ▸
       at 5 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸ done

  b6 : Chain (K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw01 ∷ Sw34 ∷ K2 ∷ ι ∷ Sw01 ∷ []) (Sw01 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2 ∷ ι ∷ Sw01 ∷ [])
  b6 = at 6 2 (Sw01 ∷ CS13 ∷ []) (wl0019 c4) ▸
       at 5 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 6 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw01 ∷ CX12 ∷ []) (wl0048 c4) ▸
       at 3 2 (Sw01 ∷ CS24⁻ ∷ []) (sym (c₂ (Swap) (Swap ↑ • (CS • CS • CS) • Swap ↑))) ▸
       at 2 2 (Sw01 ∷ CX12 ∷ []) (wl0048 c4) ▸
       at 1 2 (Sw01 ∷ CS24 ∷ []) (sym (c₂ (Swap) (Swap ↑ • CS • Swap ↑))) ▸
       at 0 2 (Sw01 ∷ K2 ∷ []) (sym (c₂ (Swap) (K))) ▸ done

  b7 : Chain (Sw01 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2 ∷ ι ∷ Sw01 ∷ []) (Sw01 ∷ Sw34 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw34 ∷ CS14 ∷ K2 ∷ ι ∷ Sw01 ∷ [])
  b7 = at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 2 2 (K2 ∷ Sw34 ∷ []) (sym (c₃ (K ↑ ↑) (Swap))) ▸
       at 4 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0007 c4) ▸
       at 4 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 6 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0007 c4) ▸
       at 6 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸ done

  b8 : Chain (Sw01 ∷ Sw34 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw34 ∷ CS14 ∷ K2 ∷ ι ∷ Sw01 ∷ []) (Sw01 ∷ Toff214 ∷ Sw01 ∷ [])
  b8 = at 8 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0007 c4) ▸
       at 8 2 (K2 ∷ Sw34 ∷ []) (sym (c₃ (K ↑ ↑) (Swap))) ▸
       at 9 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 2 8 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (wl0059 c4) ▸
       at 2 8 (Toff213 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff214 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 BOX(1;24): 2 steps
lem-nat-0-BOX⟨1·24⟩ : WsL → ⟪ (Sw01 ∷ Bx1-24 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-24 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·24⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-24 ∷ []) (Bx0-24 ∷ Sw01 ∷ [])
  b0 = at 0 2 (Bx1-24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CZ • Swap ↑)) ▸
       at 0 1 (Bx0-24 ∷ []) (by-assoc Eq.refl) ▸ done


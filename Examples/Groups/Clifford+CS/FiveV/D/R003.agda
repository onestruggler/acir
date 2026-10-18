{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.FiveV.D.R003 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.FiveV.WinSig using (WsL ; wl0002 ; wl0003 ; wl0004 ; wl0005 ; wl0006 ; wl0007 ; wl0008 ; wl0009 ; wl0011 ; wl0012 ; wl0013 ; wl0014 ; wl0016 ; wl0017 ; wl0018 ; wl0019 ; wl0020 ; wl0021 ; wl0022 ; wl0025 ; wl0028 ; wl0029 ; wl0033 ; wl0034 ; wl0035 ; wl0036 ; wl0037 ; wl0038 ; wl0039 ; wl0044 ; wl0045 ; wl0046 ; wl0047 ; wl0048 ; wl0049 ; wl0054 ; wl0055 ; wl0056 ; wl0057 ; wl0058 ; wl0059 ; wl0060 ; wl0061 ; wl0064 ; wl0065 ; wl0066 ; wl0068 ; wl0072 ; wl0074 ; wl0075 ; wl0076 ; wl0077 ; wl0078 ; wl0079 ; wl0080 ; wl0081 ; wl0082 ; wl0083 ; wl0084 ; wl0085 ; wl0086 ; wl0087 ; wl0088)
open import Examples.Groups.Clifford+CS.FiveV.Chain
open import Examples.Groups.Clifford+CS.FiveV.D.R001 using (lem-comm-push-CS04-sw0-L ; lem-comm-push-CS04-sw1-R ; lem-comm-push-CS04-sw2-L ; lem-comm-push-CS04-sw2-R ; lem-comm-push-CZ04-sw0-L ; lem-comm-push-TOFF024-sw0-L ; lem-comm-push-TOFF204-sw0-L)
open import Examples.Groups.Clifford+CS.FiveV.D.R002 using (lem-comm-push-TOFF304-sw0-L ; lem-comm-push-TOFF304-sw1-L ; lem-comm-push-TOFF402-sw0-L ; lem-comm-push-TOFF403-sw1-L)
-- comm push TOFF403 sw0 L: 86 steps
lem-comm-push-TOFF403-sw0-L : WsL → ⟪ (Toff403 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Toff413 ∷ []) ⟫ʷ
lem-comm-push-TOFF403-sw0-L c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (run b10))))))))))
  where
  b0 : Chain (Toff403 ∷ Sw01 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Toff402 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw12 ∷ Toff401 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Toff301 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (K3 ∷ Sw23 ∷ []) (sym (wl0064 c4)) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ [])
  b1 = at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K3 ∷ Sw23 ∷ []) (sym (wl0064 c4)) ▸
       at 10 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸ done

  b2 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ []) (Sw23 ∷ Sw12 ∷ K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ [])
  b2 = at 11 2 [] (wl0003 c4) ▸
       at 2 2 (K4 ∷ Sw34 ∷ []) (sym (wl0065 c4)) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 5 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸ done

  b3 : Chain (Sw23 ∷ Sw12 ∷ K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ []) (Sw23 ∷ K4 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ [])
  b3 = at 9 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 7 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K4 ∷ Sw34 ∷ []) (sym (wl0065 c4)) ▸
       at 9 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 10 2 [] (wl0004 c4) ▸
       at 1 2 (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑)) ▸
       at 2 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0005 c4)) ▸
       at 5 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸ done

  b4 : Chain (Sw23 ∷ K4 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ []) (Sw23 ∷ K4 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K4 ∷ ι ∷ Sw23 ∷ Sw01 ∷ [])
  b4 = at 3 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS24⁻ ∷ Sw12 ∷ []) (sym (wl0007 c4)) ▸
       at 7 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 5 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R c4) ▸
       at 7 2 (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑)) ▸
       at 8 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 9 2 [] (wl0006 c4) ▸ done

  b5 : Chain (Sw23 ∷ K4 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K4 ∷ ι ∷ Sw23 ∷ Sw01 ∷ []) (K4 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Sw23 ∷ K4 ∷ ι ∷ Sw23 ∷ Sw01 ∷ [])
  b5 = at 0 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸
       at 1 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0008 c4)) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 2 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0009 c4)) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS04 ∷ Sw23 ∷ []) (lem-comm-push-CS04-sw2-R c4) ▸ done

  b6 : Chain (K4 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Sw23 ∷ K4 ∷ ι ∷ Sw23 ∷ Sw01 ∷ []) (K4 ∷ CS34 ∷ CX03 ∷ Sw01 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K4 ∷ ι ∷ [])
  b6 = at 6 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸
       at 7 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 8 2 [] (wl0003 c4) ▸
       at 7 2 (Sw01 ∷ ι ∷ []) (sym (wl0025 c4)) ▸
       at 6 2 (Sw01 ∷ K4 ∷ []) (sym (c₂ (Swap) (K ↑ ↑))) ▸
       at 5 2 (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L c4) ▸
       at 4 2 (Sw01 ∷ CX13 ∷ []) (wl0016 c4) ▸
       at 3 2 (Sw01 ∷ CS34⁻ ∷ []) (sym (c₂ (Swap) ((CS • CS • CS) ↑))) ▸ done

  b7 : Chain (K4 ∷ CS34 ∷ CX03 ∷ Sw01 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K4 ∷ ι ∷ []) (Sw01 ∷ Sw23 ∷ K4 ∷ CS24 ∷ CX12 ∷ Sw23 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K4 ∷ ι ∷ [])
  b7 = at 2 2 (Sw01 ∷ CX13 ∷ []) (wl0016 c4) ▸
       at 1 2 (Sw01 ∷ CS34 ∷ []) (sym (c₂ (Swap) (CS ↑))) ▸
       at 0 2 (Sw01 ∷ K4 ∷ []) (sym (c₂ (Swap) (K ↑ ↑))) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 2 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸
       at 3 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0011 c4)) ▸
       at 5 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0003 c4) ▸ done

  b8 : Chain (Sw01 ∷ Sw23 ∷ K4 ∷ CS24 ∷ CX12 ∷ Sw23 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K4 ∷ ι ∷ []) (Sw01 ∷ Sw23 ∷ Sw34 ∷ K3 ∷ Sw34 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K4 ∷ ι ∷ Sw23 ∷ [])
  b8 = at 5 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0012 c4)) ▸
       at 7 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0003 c4) ▸
       at 7 2 (CS14 ∷ Sw23 ∷ []) (sym (wl0017 c4)) ▸
       at 8 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 2 (K3 ∷ Sw34 ∷ []) (sym (wl0066 c4)) ▸ done

  b9 : Chain (Sw01 ∷ Sw23 ∷ Sw34 ∷ K3 ∷ Sw34 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K4 ∷ ι ∷ Sw23 ∷ []) (Sw01 ∷ Sw23 ∷ Sw34 ∷ K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw34 ∷ K4 ∷ ι ∷ Sw23 ∷ [])
  b9 = at 5 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0004 c4) ▸
       at 5 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 7 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0004 c4) ▸
       at 7 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 9 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0004 c4) ▸ done

  b10 : Chain (Sw01 ∷ Sw23 ∷ Sw34 ∷ K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw34 ∷ K4 ∷ ι ∷ Sw23 ∷ []) (Sw01 ∷ Toff413 ∷ [])
  b10 = at 9 2 (K3 ∷ Sw34 ∷ []) (sym (wl0066 c4)) ▸
       at 10 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 3 8 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) (wl0068 c4) ▸
       at 3 8 (Toff312 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff412 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff413 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp TOFF402 at 3: 7 steps
lem-resp-TOFF402-at-3 : WsL → ⟪ (Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff413 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-TOFF402-at-3 c4 = run b0
  where
  b0 : Chain (Toff402 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff413 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (Toff403 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 1 2 (Sw12 ∷ Toff403 ∷ []) (lem-comm-push-TOFF403-sw1-L c4) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 2 2 (Sw01 ∷ Toff413 ∷ []) (lem-comm-push-TOFF403-sw0-L c4) ▸ done


-- resp CX42 at 3: 6 steps
lem-resp-CX42-at-3 : WsL → ⟪ (CX42 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CX43 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CX42-at-3 c4 = run b0
  where
  b0 : Chain (CX42 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CX43 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 0 2 (Sw23 ∷ CX43 ∷ []) (wl0058 c4) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 1 2 (Sw12 ∷ CX43 ∷ []) (sym (c₃ (Swap ↑) (CX₁₀))) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 2 2 (Sw01 ∷ CX43 ∷ []) (sym (c₂ (Swap) (CX₁₀ ↑))) ▸ done


-- resp CSd14 at 3: 6 steps
lem-resp-CSd14-at-3 : WsL → ⟪ (CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CS24⁻ ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CSd14-at-3 c4 = run b0
  where
  b0 : Chain (CS14⁻ ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CS24⁻ ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 0 2 (Sw23 ∷ CS14⁻ ∷ []) (wl0048 c4) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 1 2 (Sw12 ∷ CS24⁻ ∷ []) (wl0014 c4) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 2 2 (Sw01 ∷ CS24⁻ ∷ []) (sym (c₂ (Swap) (Swap ↑ • (CS • CS • CS) • Swap ↑))) ▸ done


-- resp CX24 at 3: 6 steps
lem-resp-CX24-at-3 : WsL → ⟪ (CX24 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CX34 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CX24-at-3 c4 = run b0
  where
  b0 : Chain (CX24 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CX34 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 0 2 (Sw23 ∷ CX34 ∷ []) (wl0020 c4) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 1 2 (Sw12 ∷ CX34 ∷ []) (sym (c₃ (Swap ↑) (CX₀₁))) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 2 2 (Sw01 ∷ CX34 ∷ []) (sym (c₂ (Swap) (CX₀₁ ↑))) ▸ done


-- resp TOFF304 at 1: 2 steps
lem-resp-TOFF304-at-1 : WsL → ⟪ (Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Toff314 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-TOFF304-at-1 c4 = run b0
  where
  b0 : Chain (Toff304 ∷ []) (Sw01 ∷ Toff314 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 0 2 (Sw01 ∷ Toff314 ∷ []) (lem-comm-push-TOFF304-sw0-L c4) ▸ done


-- comm SWAP24 BOX(0;31): 7 steps
lem-comm-SWAP24-BOX⟨0·31⟩ : WsL → ⟪ (Sw24 ∷ Bx0-31 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-31 ∷ Sw24 ∷ []) ⟫ʷ
lem-comm-SWAP24-BOX⟨0·31⟩ c4 = run b0
  where
  b0 : Chain (Sw24 ∷ Bx0-31 ∷ []) (Bx0-31 ∷ Sw24 ∷ [])
  b0 = at 1 1 (CZ13 ∷ []) (refl) ▸
       at 1 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ Sw34 ∷ []) (sym (wl0055 c4)) ▸
       at 1 2 (CZ12 ∷ Sw34 ∷ []) (sym (c₃ (CZ ↑) (Swap))) ▸
       at 2 2 (Sw23 ∷ Sw24 ∷ []) (sym (wl0056 c4)) ▸
       at 0 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸
       at 0 1 (Bx0-31 ∷ []) (refl) ▸ done


-- comm CX31 CCZ024: 11 steps
lem-comm-CX31-CCZ024 : WsL → ⟪ (CX31 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ CX31 ∷ []) ⟫ʷ
lem-comm-CX31-CCZ024 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX31 ∷ CCZ024 ∷ []) (Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ CX32 ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ CX32 ∷ []) (wl0057 c4) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 3 (CX42 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw23 ∷ CX43 ∷ []) (wl0058 c4) ▸
       at 3 2 (CCZ012 ∷ CX43 ∷ []) (sym (c₃ (CCZ) (CX₁₀))) ▸
       at 4 2 (Sw23 ∷ CX42 ∷ []) (wl0059 c4) ▸
       at 5 1 (Sw34 ∷ CX32 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ CX32 ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ []) (CCZ024 ∷ CX31 ∷ [])
  b1 = at 7 2 [] (wl0004 c4) ▸
       at 6 2 (Sw12 ∷ CX31 ∷ []) (wl0060 c4) ▸
       at 0 7 (CCZ024 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp TOFF401 at 2: 5 steps
lem-resp-TOFF401-at-2 : WsL → ⟪ (Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ Toff412 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-TOFF401-at-2 c4 = run b0
  where
  b0 : Chain (Toff401 ∷ []) (Sw12 ∷ Sw01 ∷ Toff412 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 1 3 (Toff402 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 1 2 (Sw01 ∷ Toff412 ∷ []) (lem-comm-push-TOFF402-sw0-L c4) ▸ done


-- comm CS13 TOFF024: 11 steps
lem-comm-CS13-TOFF024 : WsL → ⟪ (CS13 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CS13 ∷ []) ⟫ʷ
lem-comm-CS13-TOFF024 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS13 ∷ Toff024 ∷ []) (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ CS23 ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ CS23 ∷ []) (wl0046 c4) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 3 (CS24 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw23 ∷ CS34 ∷ []) (wl0011 c4) ▸
       at 3 2 (Toff012 ∷ CS34 ∷ []) (sym (c₃ (Toff) (CS))) ▸
       at 4 2 (Sw23 ∷ CS24 ∷ []) (wl0008 c4) ▸
       at 5 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ CS23 ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ []) (Toff024 ∷ CS13 ∷ [])
  b1 = at 7 2 [] (wl0004 c4) ▸
       at 6 2 (Sw12 ∷ CS13 ∷ []) (wl0047 c4) ▸
       at 0 7 (Toff024 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp SWAP14 at 3: 6 steps
lem-resp-SWAP14-at-3 : WsL → ⟪ (Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ Sw24 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-SWAP14-at-3 c4 = run b0
  where
  b0 : Chain (Sw14 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ Sw24 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 0 2 (Sw23 ∷ Sw14 ∷ []) (wl0074 c4) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 1 2 (Sw12 ∷ Sw24 ∷ []) (sym (wl0072 c4)) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 2 2 (Sw01 ∷ Sw24 ∷ []) (sym (c₂ (Swap) (Swap ↑ • Swap • Swap ↑))) ▸ done


-- resp TOFF204 at 3: 7 steps
lem-resp-TOFF204-at-3 : WsL → ⟪ (Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff314 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-TOFF204-at-3 c4 = run b0
  where
  b0 : Chain (Toff204 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff314 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (Toff304 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 1 2 (Sw12 ∷ Toff304 ∷ []) (lem-comm-push-TOFF304-sw1-L c4) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 2 2 (Sw01 ∷ Toff314 ∷ []) (lem-comm-push-TOFF304-sw0-L c4) ▸ done


-- comm SWAP14 BOX(0;23): 3 steps
lem-comm-SWAP14-BOX⟨0·23⟩ : WsL → ⟪ (Sw14 ∷ Bx0-23 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-23 ∷ Sw14 ∷ []) ⟫ʷ
lem-comm-SWAP14-BOX⟨0·23⟩ c4 = run b0
  where
  b0 : Chain (Sw14 ∷ Bx0-23 ∷ []) (Bx0-23 ∷ Sw14 ∷ [])
  b0 = at 1 1 (CZ23 ∷ []) (refl) ▸
       at 0 2 (CZ23 ∷ Sw14 ∷ []) (sym (wl0061 c4)) ▸
       at 0 1 (Bx0-23 ∷ []) (refl) ▸ done


-- comm push TOFF014 sw2 L: 62 steps
lem-comm-push-TOFF014-sw2-L : WsL → ⟪ (Toff014 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Toff014 ∷ []) ⟫ʷ
lem-comm-push-TOFF014-sw2-L c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (Toff014 ∷ Sw23 ∷ []) (Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw23 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸ done

  b1 : Chain (Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (K0 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw23 ∷ [])
  b1 = at 4 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 9 2 [] (wl0003 c4) ▸
       at 0 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸ done

  b2 : Chain (K0 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw23 ∷ []) (K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw23 ∷ [])
  b2 = at 3 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 5 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw23 ∷ []) (K0 ∷ CS14 ∷ CX01 ∷ Sw23 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ [])
  b3 = at 6 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 7 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 8 2 [] (wl0004 c4) ▸
       at 7 2 (Sw23 ∷ ι ∷ []) (c₁ (iI) (Swap ↑)) ▸
       at 6 2 (Sw23 ∷ K0 ∷ []) (c₁ (K) (Swap ↑)) ▸
       at 5 2 (Sw23 ∷ CS04 ∷ []) (lem-comm-push-CS04-sw2-L c4) ▸
       at 4 2 (Sw23 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Swap)) ▸
       at 3 2 (Sw23 ∷ CS14⁻ ∷ []) (wl0048 c4) ▸ done

  b4 : Chain (K0 ∷ CS14 ∷ CX01 ∷ Sw23 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ []) (Sw23 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw34 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ [])
  b4 = at 2 2 (Sw23 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Swap)) ▸
       at 1 2 (Sw23 ∷ CS14 ∷ []) (wl0017 c4) ▸
       at 0 2 (Sw23 ∷ K0 ∷ []) (c₁ (K) (Swap ↑)) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 4 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0004 c4) ▸
       at 4 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸ done

  b5 : Chain (Sw23 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw34 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ []) (Sw23 ∷ Sw34 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ [])
  b5 = at 6 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0004 c4) ▸
       at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0004 c4) ▸
       at 8 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 9 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸ done

  b6 : Chain (Sw23 ∷ Sw34 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ []) (Sw23 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw34 ∷ [])
  b6 = at 3 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0003 c4) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0003 c4) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b7 : Chain (Sw23 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw34 ∷ []) (Sw23 ∷ Toff014 ∷ [])
  b7 = at 8 2 [] (wl0003 c4) ▸
       at 9 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 10 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 3 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff014 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp TOFF014 at 3: 7 steps
lem-resp-TOFF014-at-3 : WsL → ⟪ (Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff124 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-TOFF014-at-3 c4 = run b0
  where
  b0 : Chain (Toff014 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff124 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 0 2 (Sw23 ∷ Toff014 ∷ []) (lem-comm-push-TOFF014-sw2-L c4) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 2 3 (Toff024 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 2 2 (Sw01 ∷ Toff124 ∷ []) (lem-comm-push-TOFF024-sw0-L c4) ▸ done


-- resp SWAP13 at 2: 4 steps
lem-resp-SWAP13-at-2 : WsL → ⟪ (Sw13 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-SWAP13-at-2 c4 = run b0
  where
  b0 : Chain (Sw13 ∷ []) (Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 0 2 (Sw12 ∷ Sw23 ∷ []) (sym (wl0075 c4)) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 1 2 (Sw01 ∷ Sw23 ∷ []) (sym (c₂ (Swap) (Swap))) ▸ done


-- resp TOFF403 at 2: 4 steps
lem-resp-TOFF403-at-2 : WsL → ⟪ (Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ Toff413 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-TOFF403-at-2 c4 = run b0
  where
  b0 : Chain (Toff403 ∷ []) (Sw12 ∷ Sw01 ∷ Toff413 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 0 2 (Sw12 ∷ Toff403 ∷ []) (lem-comm-push-TOFF403-sw1-L c4) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 1 2 (Sw01 ∷ Toff413 ∷ []) (lem-comm-push-TOFF403-sw0-L c4) ▸ done


-- comm SWAP13 BOX(0;42): 9 steps
lem-comm-SWAP13-BOX⟨0·42⟩ : WsL → ⟪ (Sw13 ∷ Bx0-42 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-42 ∷ Sw13 ∷ []) ⟫ʷ
lem-comm-SWAP13-BOX⟨0·42⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw13 ∷ Bx0-42 ∷ []) (CZ24 ∷ Sw13 ∷ [])
  b0 = at 1 1 (CZ24 ∷ []) (refl) ▸
       at 1 1 (Sw34 ∷ CZ23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 3 (Sw14 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (CZ23 ∷ Sw14 ∷ []) (sym (wl0061 c4)) ▸
       at 2 1 (Sw34 ∷ Sw13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0004 c4) ▸
       at 0 3 (CZ24 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (CZ24 ∷ Sw13 ∷ []) (Bx0-42 ∷ Sw13 ∷ [])
  b1 = at 0 1 (Bx0-42 ∷ []) (refl) ▸ done


-- comm TOFF034 CSd12: 15 steps
lem-comm-TOFF034-CSd12 : WsL → ⟪ (Toff034 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ Toff034 ∷ []) ⟫ʷ
lem-comm-TOFF034-CSd12 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff034 ∷ CS12⁻ ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CS34⁻ ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 8 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CS23⁻ ∷ Sw12 ∷ []) (sym (wl0029 c4)) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 6 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0009 c4)) ▸
       at 4 2 (CS34⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (CS • CS • CS)) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CS34⁻ ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (CS12⁻ ∷ Toff034 ∷ [])
  b1 = at 3 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0012 c4)) ▸
       at 3 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0004 c4) ▸
       at 1 2 (CS13⁻ ∷ Sw12 ∷ []) (sym (wl0028 c4)) ▸
       at 1 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0003 c4) ▸
       at 1 9 (Toff034 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp TOFF104 at 2: 5 steps
lem-resp-TOFF104-at-2 : WsL → ⟪ (Toff104 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ Toff214 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-TOFF104-at-2 c4 = run b0
  where
  b0 : Chain (Toff104 ∷ []) (Sw12 ∷ Sw01 ∷ Toff214 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 1 3 (Toff204 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 1 2 (Sw01 ∷ Toff214 ∷ []) (lem-comm-push-TOFF204-sw0-L c4) ▸ done


-- resp CZ13 at 2: 4 steps
lem-resp-CZ13-at-2 : WsL → ⟪ (CZ13 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CZ23 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CZ13-at-2 c4 = run b0
  where
  b0 : Chain (CZ13 ∷ []) (Sw12 ∷ Sw01 ∷ CZ23 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 0 2 (Sw12 ∷ CZ23 ∷ []) (wl0033 c4) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 1 2 (Sw01 ∷ CZ23 ∷ []) (sym (c₂ (Swap) (CZ))) ▸ done


-- comm push TOFF104 sw2 L: 62 steps
lem-comm-push-TOFF104-sw2-L : WsL → ⟪ (Toff104 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Toff104 ∷ []) ⟫ʷ
lem-comm-push-TOFF104-sw2-L c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (Toff104 ∷ Sw23 ∷ []) (Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw23 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Toff103 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸ done

  b1 : Chain (Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (K1 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw23 ∷ [])
  b1 = at 4 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 9 2 [] (wl0003 c4) ▸
       at 0 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸ done

  b2 : Chain (K1 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw23 ∷ []) (K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw34 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw23 ∷ [])
  b2 = at 3 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 5 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw34 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw23 ∷ []) (K1 ∷ CS14 ∷ CX01 ∷ Sw23 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ [])
  b3 = at 6 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 7 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 8 2 [] (wl0004 c4) ▸
       at 7 2 (Sw23 ∷ ι ∷ []) (c₁ (iI) (Swap ↑)) ▸
       at 6 2 (Sw23 ∷ K1 ∷ []) (c₂ (K ↑) (Swap)) ▸
       at 5 2 (Sw23 ∷ CS04 ∷ []) (lem-comm-push-CS04-sw2-L c4) ▸
       at 4 2 (Sw23 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Swap)) ▸
       at 3 2 (Sw23 ∷ CS14⁻ ∷ []) (wl0048 c4) ▸ done

  b4 : Chain (K1 ∷ CS14 ∷ CX01 ∷ Sw23 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ []) (Sw23 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ Sw34 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ [])
  b4 = at 2 2 (Sw23 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Swap)) ▸
       at 1 2 (Sw23 ∷ CS14 ∷ []) (wl0017 c4) ▸
       at 0 2 (Sw23 ∷ K1 ∷ []) (c₂ (K ↑) (Swap)) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 4 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0004 c4) ▸
       at 4 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸ done

  b5 : Chain (Sw23 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ Sw34 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ []) (Sw23 ∷ Sw34 ∷ Sw23 ∷ Sw23 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ [])
  b5 = at 6 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0004 c4) ▸
       at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0004 c4) ▸
       at 8 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 9 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸ done

  b6 : Chain (Sw23 ∷ Sw34 ∷ Sw23 ∷ Sw23 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ []) (Sw23 ∷ Sw34 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ K1 ∷ ι ∷ Sw34 ∷ [])
  b6 = at 3 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0003 c4) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0003 c4) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b7 : Chain (Sw23 ∷ Sw34 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ K1 ∷ ι ∷ Sw34 ∷ []) (Sw23 ∷ Toff104 ∷ [])
  b7 = at 8 2 [] (wl0003 c4) ▸
       at 9 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 10 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 3 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff103 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff104 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp TOFF104 at 3: 7 steps
lem-resp-TOFF104-at-3 : WsL → ⟪ (Toff104 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff214 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-TOFF104-at-3 c4 = run b0
  where
  b0 : Chain (Toff104 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff214 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 0 2 (Sw23 ∷ Toff104 ∷ []) (lem-comm-push-TOFF104-sw2-L c4) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 2 3 (Toff204 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 2 2 (Sw01 ∷ Toff214 ∷ []) (lem-comm-push-TOFF204-sw0-L c4) ▸ done


-- comm CX42 CCZ013: 5 steps
lem-comm-CX42-CCZ013 : WsL → ⟪ (CX42 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ CX42 ∷ []) ⟫ʷ
lem-comm-CX42-CCZ013 c4 = run b0
  where
  b0 : Chain (CX42 ∷ CCZ013 ∷ []) (CCZ013 ∷ CX42 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ CX43 ∷ []) (wl0058 c4) ▸
       at 1 2 (CCZ012 ∷ CX43 ∷ []) (sym (c₃ (CCZ) (CX₁₀))) ▸
       at 2 2 (Sw23 ∷ CX42 ∷ []) (wl0059 c4) ▸
       at 0 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CX32 CCZ014: 9 steps
lem-comm-CX32-CCZ014 : WsL → ⟪ (CX32 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ CX32 ∷ []) ⟫ʷ
lem-comm-CX32-CCZ014 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX32 ∷ CCZ014 ∷ []) (Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ CX32 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 3 (CX42 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw23 ∷ CX43 ∷ []) (wl0058 c4) ▸
       at 2 2 (CCZ012 ∷ CX43 ∷ []) (sym (c₃ (CCZ) (CX₁₀))) ▸
       at 3 2 (Sw23 ∷ CX42 ∷ []) (wl0059 c4) ▸
       at 4 1 (Sw34 ∷ CX32 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0004 c4) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ CX32 ∷ []) (CCZ014 ∷ CX32 ∷ [])
  b1 = at 0 5 (CCZ014 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp TOFF402 at 1: 2 steps
lem-resp-TOFF402-at-1 : WsL → ⟪ (Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Toff412 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-TOFF402-at-1 c4 = run b0
  where
  b0 : Chain (Toff402 ∷ []) (Sw01 ∷ Toff412 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 0 2 (Sw01 ∷ Toff412 ∷ []) (lem-comm-push-TOFF402-sw0-L c4) ▸ done


-- comm CSd12 CCZ034: 15 steps
lem-comm-CSd12-CCZ034 : WsL → ⟪ (CS12⁻ ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CS12⁻ ∷ []) ⟫ʷ
lem-comm-CSd12-CCZ034 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS12⁻ ∷ CCZ034 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ CS34⁻ ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw12 ∷ CS23⁻ ∷ []) (wl0028 c4) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw23 ∷ CS34⁻ ∷ []) (wl0012 c4) ▸
       at 4 2 (CCZ012 ∷ CS34⁻ ∷ []) (sym (c₃ (CCZ) (CS • CS • CS))) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ CS34⁻ ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (CCZ034 ∷ CS12⁻ ∷ [])
  b1 = at 5 2 (Sw23 ∷ CS24⁻ ∷ []) (wl0009 c4) ▸
       at 6 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0004 c4) ▸
       at 7 2 (Sw12 ∷ CS13⁻ ∷ []) (wl0029 c4) ▸
       at 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (wl0003 c4) ▸
       at 0 9 (CCZ034 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CS12 CCZ034: 15 steps
lem-comm-CS12-CCZ034 : WsL → ⟪ (CS12 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CS12 ∷ []) ⟫ʷ
lem-comm-CS12-CCZ034 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS12 ∷ CCZ034 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ CS34 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw12 ∷ CS23 ∷ []) (wl0046 c4) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (CS24 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw23 ∷ CS34 ∷ []) (wl0011 c4) ▸
       at 4 2 (CCZ012 ∷ CS34 ∷ []) (sym (c₃ (CCZ) (CS))) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ CS34 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (CCZ034 ∷ CS12 ∷ [])
  b1 = at 5 2 (Sw23 ∷ CS24 ∷ []) (wl0008 c4) ▸
       at 6 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0004 c4) ▸
       at 7 2 (Sw12 ∷ CS13 ∷ []) (wl0047 c4) ▸
       at 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (wl0003 c4) ▸
       at 0 9 (CCZ034 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CZ02 at 1: 2 steps
lem-resp-CZ02-at-1 : WsL → ⟪ (CZ02 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CZ12 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CZ02-at-1 c4 = run b0
  where
  b0 : Chain (CZ02 ∷ []) (Sw01 ∷ CZ12 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 0 2 (Sw01 ∷ CZ12 ∷ []) (wl0076 c4) ▸ done


-- resp CX20 at 1: 2 steps
lem-resp-CX20-at-1 : WsL → ⟪ (CX20 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CX21 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CX20-at-1 c4 = run b0
  where
  b0 : Chain (CX20 ∷ []) (Sw01 ∷ CX21 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 0 2 (Sw01 ∷ CX21 ∷ []) (wl0077 c4) ▸ done


-- resp CX03 at 1: 2 steps
lem-resp-CX03-at-1 : WsL → ⟪ (CX03 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CX13 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CX03-at-1 c4 = run b0
  where
  b0 : Chain (CX03 ∷ []) (Sw01 ∷ CX13 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 0 2 (Sw01 ∷ CX13 ∷ []) (wl0016 c4) ▸ done


-- resp CZ03 at 1: 2 steps
lem-resp-CZ03-at-1 : WsL → ⟪ (CZ03 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CZ13 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CZ03-at-1 c4 = run b0
  where
  b0 : Chain (CZ03 ∷ []) (Sw01 ∷ CZ13 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 0 2 (Sw01 ∷ CZ13 ∷ []) (wl0049 c4) ▸ done


-- comm CX12 TOFF034: 15 steps
lem-comm-CX12-TOFF034 : WsL → ⟪ (CX12 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CX12 ∷ []) ⟫ʷ
lem-comm-CX12-TOFF034 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX12 ∷ Toff034 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ CX34 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw12 ∷ CX23 ∷ []) (wl0019 c4) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (CX24 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw23 ∷ CX34 ∷ []) (wl0020 c4) ▸
       at 4 2 (Toff012 ∷ CX34 ∷ []) (sym (c₃ (Toff) (CX₀₁))) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ CX34 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Toff034 ∷ CX12 ∷ [])
  b1 = at 5 2 (Sw23 ∷ CX24 ∷ []) (wl0021 c4) ▸
       at 6 1 (Sw34 ∷ CX23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0004 c4) ▸
       at 7 2 (Sw12 ∷ CX13 ∷ []) (wl0022 c4) ▸
       at 8 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (wl0003 c4) ▸
       at 0 9 (Toff034 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CX30 at 1: 2 steps
lem-resp-CX30-at-1 : WsL → ⟪ (CX30 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CX31 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CX30-at-1 c4 = run b0
  where
  b0 : Chain (CX30 ∷ []) (Sw01 ∷ CX31 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 0 2 (Sw01 ∷ CX31 ∷ []) (wl0078 c4) ▸ done


-- comm push CZ04 sw2 L: 7 steps
lem-comm-push-CZ04-sw2-L : WsL → ⟪ (CZ04 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ CZ04 ∷ []) ⟫ʷ
lem-comm-push-CZ04-sw2-L c4 = run b0
  where
  b0 : Chain (CZ04 ∷ Sw23 ∷ []) (Sw23 ∷ CZ04 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0002 c4) ▸
       at 4 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 3 2 (Sw34 ∷ CZ01 ∷ []) (c₂ (CZ) (Swap ↑)) ▸
       at 2 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 0 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (sym (wl0002 c4)) ▸
       at 1 7 (CZ04 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm push CZ04 sw1 L: 5 steps
lem-comm-push-CZ04-sw1-L : WsL → ⟪ (CZ04 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CZ04 ∷ []) ⟫ʷ
lem-comm-push-CZ04-sw1-L c4 = run b0
  where
  b0 : Chain (CZ04 ∷ Sw12 ∷ []) (Sw12 ∷ CZ04 ∷ [])
  b0 = at 0 1 (Sw34 ∷ CZ03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 1 2 (Sw12 ∷ CZ03 ∷ []) (wl0079 c4) ▸
       at 0 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 1 3 (CZ04 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CZ04 at 3: 6 steps
lem-resp-CZ04-at-3 : WsL → ⟪ (CZ04 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CZ14 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CZ04-at-3 c4 = run b0
  where
  b0 : Chain (CZ04 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CZ14 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 0 2 (Sw23 ∷ CZ04 ∷ []) (lem-comm-push-CZ04-sw2-L c4) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 1 2 (Sw12 ∷ CZ04 ∷ []) (lem-comm-push-CZ04-sw1-L c4) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 2 2 (Sw01 ∷ CZ14 ∷ []) (lem-comm-push-CZ04-sw0-L c4) ▸ done


-- comm push CX40 sw2 L: 7 steps
lem-comm-push-CX40-sw2-L : WsL → ⟪ (CX40 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ CX40 ∷ []) ⟫ʷ
lem-comm-push-CX40-sw2-L c4 = run b0
  where
  b0 : Chain (CX40 ∷ Sw23 ∷ []) (Sw23 ∷ CX40 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0002 c4) ▸
       at 4 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 3 2 (Sw34 ∷ CX10 ∷ []) (c₂ (CX₁₀) (Swap ↑)) ▸
       at 2 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 0 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (sym (wl0002 c4)) ▸
       at 1 7 (CX40 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm push CX40 sw1 L: 5 steps
lem-comm-push-CX40-sw1-L : WsL → ⟪ (CX40 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CX40 ∷ []) ⟫ʷ
lem-comm-push-CX40-sw1-L c4 = run b0
  where
  b0 : Chain (CX40 ∷ Sw12 ∷ []) (Sw12 ∷ CX40 ∷ [])
  b0 = at 0 1 (Sw34 ∷ CX30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 1 2 (Sw12 ∷ CX30 ∷ []) (wl0080 c4) ▸
       at 0 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 1 3 (CX40 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm push CX40 sw0 L: 5 steps
lem-comm-push-CX40-sw0-L : WsL → ⟪ (CX40 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CX41 ∷ []) ⟫ʷ
lem-comm-push-CX40-sw0-L c4 = run b0
  where
  b0 : Chain (CX40 ∷ Sw01 ∷ []) (Sw01 ∷ CX41 ∷ [])
  b0 = at 0 1 (Sw34 ∷ CX30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 1 2 (Sw01 ∷ CX31 ∷ []) (wl0078 c4) ▸
       at 0 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 1 3 (CX41 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CX40 at 3: 6 steps
lem-resp-CX40-at-3 : WsL → ⟪ (CX40 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CX41 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CX40-at-3 c4 = run b0
  where
  b0 : Chain (CX40 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CX41 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 0 2 (Sw23 ∷ CX40 ∷ []) (lem-comm-push-CX40-sw2-L c4) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 1 2 (Sw12 ∷ CX40 ∷ []) (lem-comm-push-CX40-sw1-L c4) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 2 2 (Sw01 ∷ CX41 ∷ []) (lem-comm-push-CX40-sw0-L c4) ▸ done


-- resp CX40 at 1: 2 steps
lem-resp-CX40-at-1 : WsL → ⟪ (CX40 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CX41 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CX40-at-1 c4 = run b0
  where
  b0 : Chain (CX40 ∷ []) (Sw01 ∷ CX41 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 0 2 (Sw01 ∷ CX41 ∷ []) (lem-comm-push-CX40-sw0-L c4) ▸ done


-- comm push CK40 sw0 L: 5 steps
lem-comm-push-CK40-sw0-L : WsL → ⟪ (CK40 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CK41 ∷ []) ⟫ʷ
lem-comm-push-CK40-sw0-L c4 = run b0
  where
  b0 : Chain (CK40 ∷ Sw01 ∷ []) (Sw01 ∷ CK41 ∷ [])
  b0 = at 0 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 1 2 (Sw01 ∷ CK31 ∷ []) (wl0081 c4) ▸
       at 0 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 1 3 (CK41 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CK40 at 1: 2 steps
lem-resp-CK40-at-1 : WsL → ⟪ (CK40 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CK41 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CK40-at-1 c4 = run b0
  where
  b0 : Chain (CK40 ∷ []) (Sw01 ∷ CK41 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 0 2 (Sw01 ∷ CK41 ∷ []) (lem-comm-push-CK40-sw0-L c4) ▸ done


-- comm push CKd40 sw0 L: 5 steps
lem-comm-push-CKd40-sw0-L : WsL → ⟪ (CK40⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CK41⁻ ∷ []) ⟫ʷ
lem-comm-push-CKd40-sw0-L c4 = run b0
  where
  b0 : Chain (CK40⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CK41⁻ ∷ [])
  b0 = at 0 1 (Sw34 ∷ CK30⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 1 2 (Sw01 ∷ CK31⁻ ∷ []) (wl0082 c4) ▸
       at 0 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 1 3 (CK41⁻ ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CKd40 at 1: 2 steps
lem-resp-CKd40-at-1 : WsL → ⟪ (CK40⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CK41⁻ ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CKd40-at-1 c4 = run b0
  where
  b0 : Chain (CK40⁻ ∷ []) (Sw01 ∷ CK41⁻ ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 0 2 (Sw01 ∷ CK41⁻ ∷ []) (lem-comm-push-CKd40-sw0-L c4) ▸ done


-- resp CZ04 at 2: 4 steps
lem-resp-CZ04-at-2 : WsL → ⟪ (CZ04 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CZ14 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CZ04-at-2 c4 = run b0
  where
  b0 : Chain (CZ04 ∷ []) (Sw12 ∷ Sw01 ∷ CZ14 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 0 2 (Sw12 ∷ CZ04 ∷ []) (lem-comm-push-CZ04-sw1-L c4) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 1 2 (Sw01 ∷ CZ14 ∷ []) (lem-comm-push-CZ04-sw0-L c4) ▸ done


-- comm CX02 CCZ134: 23 steps
lem-comm-CX02-CCZ134 : WsL → ⟪ (CX02 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CX02 ∷ []) ⟫ʷ
lem-comm-CX02-CCZ134 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX02 ∷ CCZ134 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ CCZ124 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 3 (CX04 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 8 3 (CCZ124 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ CCZ124 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b1 = at 9 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 7 3 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0044 c4)) ▸
       at 5 2 (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ)) ▸
       at 4 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 4 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0003 c4) ▸
       at 3 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (CCZ134 ∷ CX02 ∷ [])
  b2 = at 2 2 [] (wl0004 c4) ▸
       at 3 7 (CX04 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0004 c4) ▸
       at 4 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0003 c4) ▸
       at 0 5 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CSd02 TOFF134: 23 steps
lem-comm-CSd02-TOFF134 : WsL → ⟪ (CS02⁻ ∷ Toff134 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-comm-CSd02-TOFF134 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS02⁻ ∷ Toff134 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Toff124 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw34 ∷ Toff123 ∷ Sw34 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 3 (CS04⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 8 3 (Toff124 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Toff124 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Toff123 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b1 = at 9 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 7 3 (Toff134 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Toff234 ∷ Sw12 ∷ []) (wl0083 c4) ▸
       at 5 2 (Toff234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (Toff)) ▸
       at 4 2 (Toff134 ∷ Sw12 ∷ []) (wl0054 c4) ▸
       at 4 1 (Sw23 ∷ Toff124 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0003 c4) ▸
       at 3 1 (Sw34 ∷ Toff123 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Toff123 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (Toff134 ∷ CS02⁻ ∷ [])
  b2 = at 2 2 [] (wl0004 c4) ▸
       at 3 7 (CS04⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ CS03⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0004 c4) ▸
       at 4 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0003 c4) ▸
       at 0 5 (Toff134 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CX02 TOFF134: 23 steps
lem-comm-CX02-TOFF134 : WsL → ⟪ (CX02 ∷ Toff134 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CX02 ∷ []) ⟫ʷ
lem-comm-CX02-TOFF134 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX02 ∷ Toff134 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Toff124 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw34 ∷ Toff123 ∷ Sw34 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 3 (CX04 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 8 3 (Toff124 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Toff124 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Toff123 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b1 = at 9 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 7 3 (Toff134 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Toff234 ∷ Sw12 ∷ []) (wl0083 c4) ▸
       at 5 2 (Toff234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Toff)) ▸
       at 4 2 (Toff134 ∷ Sw12 ∷ []) (wl0054 c4) ▸
       at 4 1 (Sw23 ∷ Toff124 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0003 c4) ▸
       at 3 1 (Sw34 ∷ Toff123 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Toff123 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (Toff134 ∷ CX02 ∷ [])
  b2 = at 2 2 [] (wl0004 c4) ▸
       at 3 7 (CX04 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0004 c4) ▸
       at 4 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0003 c4) ▸
       at 0 5 (Toff134 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CS14 TOFF023: 7 steps
lem-comm-CS14-TOFF023 : WsL → ⟪ (CS14 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CS14 ∷ []) ⟫ʷ
lem-comm-CS14-TOFF023 c4 = run b0
  where
  b0 : Chain (CS14 ∷ Toff023 ∷ []) (Toff023 ∷ CS14 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ CS24 ∷ []) (wl0013 c4) ▸
       at 1 2 (Sw23 ∷ CS34 ∷ []) (wl0011 c4) ▸
       at 2 2 (Toff012 ∷ CS34 ∷ []) (sym (c₃ (Toff) (CS))) ▸
       at 3 2 (Sw23 ∷ CS24 ∷ []) (wl0008 c4) ▸
       at 4 2 (Sw12 ∷ CS14 ∷ []) (wl0005 c4) ▸
       at 0 5 (Toff023 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CS24 TOFF013: 5 steps
lem-comm-CS24-TOFF013 : WsL → ⟪ (CS24 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CS24 ∷ []) ⟫ʷ
lem-comm-CS24-TOFF013 c4 = run b0
  where
  b0 : Chain (CS24 ∷ Toff013 ∷ []) (Toff013 ∷ CS24 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ CS34 ∷ []) (wl0011 c4) ▸
       at 1 2 (Toff012 ∷ CS34 ∷ []) (sym (c₃ (Toff) (CS))) ▸
       at 2 2 (Sw23 ∷ CS24 ∷ []) (wl0008 c4) ▸
       at 0 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm TOFF301 CSd24: 15 steps
lem-comm-TOFF301-CSd24 : WsL → ⟪ (Toff301 ∷ CS24⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS24⁻ ∷ Toff301 ∷ []) ⟫ʷ
lem-comm-TOFF301-CSd24 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff301 ∷ CS24⁻ ∷ []) (Sw34 ∷ Sw34 ∷ Sw23 ∷ CS34⁻ ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 3 (Toff401 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 5 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0009 c4)) ▸
       at 3 2 (CS34⁻ ∷ Toff201 ∷ []) (c₃ (Toffᵗ) (CS • CS • CS)) ▸ done

  b1 : Chain (Sw34 ∷ Sw34 ∷ Sw23 ∷ CS34⁻ ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ []) (CS24⁻ ∷ Toff301 ∷ [])
  b1 = at 2 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0012 c4)) ▸
       at 2 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0004 c4) ▸
       at 2 5 (Toff401 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Toff301 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0004 c4) ▸
       at 0 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CX02 at 1: 2 steps
lem-resp-CX02-at-1 : WsL → ⟪ (CX02 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CX12 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CX02-at-1 c4 = run b0
  where
  b0 : Chain (CX02 ∷ []) (Sw01 ∷ CX12 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 0 2 (Sw01 ∷ CX12 ∷ []) (wl0039 c4) ▸ done


-- comm CSd24 CCZ013: 5 steps
lem-comm-CSd24-CCZ013 : WsL → ⟪ (CS24⁻ ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ CS24⁻ ∷ []) ⟫ʷ
lem-comm-CSd24-CCZ013 c4 = run b0
  where
  b0 : Chain (CS24⁻ ∷ CCZ013 ∷ []) (CCZ013 ∷ CS24⁻ ∷ [])
  b0 = at 1 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ CS34⁻ ∷ []) (wl0012 c4) ▸
       at 1 2 (CCZ012 ∷ CS34⁻ ∷ []) (sym (c₃ (CCZ) (CS • CS • CS))) ▸
       at 2 2 (Sw23 ∷ CS24⁻ ∷ []) (wl0009 c4) ▸
       at 0 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CS24 CCZ013: 5 steps
lem-comm-CS24-CCZ013 : WsL → ⟪ (CS24 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ CS24 ∷ []) ⟫ʷ
lem-comm-CS24-CCZ013 c4 = run b0
  where
  b0 : Chain (CS24 ∷ CCZ013 ∷ []) (CCZ013 ∷ CS24 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ CS34 ∷ []) (wl0011 c4) ▸
       at 1 2 (CCZ012 ∷ CS34 ∷ []) (sym (c₃ (CCZ) (CS))) ▸
       at 2 2 (Sw23 ∷ CS24 ∷ []) (wl0008 c4) ▸
       at 0 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm TOFF401 CSd23: 9 steps
lem-comm-TOFF401-CSd23 : WsL → ⟪ (Toff401 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ Toff401 ∷ []) ⟫ʷ
lem-comm-TOFF401-CSd23 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff401 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 4 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0009 c4)) ▸
       at 2 2 (CS34⁻ ∷ Toff201 ∷ []) (c₃ (Toffᵗ) (CS • CS • CS)) ▸
       at 1 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0012 c4)) ▸
       at 1 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0004 c4) ▸ done

  b1 : Chain (CS23⁻ ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ []) (CS23⁻ ∷ Toff401 ∷ [])
  b1 = at 1 5 (Toff401 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CS03 TOFF412: 9 steps
lem-comm-CS03-TOFF412 : WsL → ⟪ (CS03 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CS03 ∷ []) ⟫ʷ
lem-comm-CS03-TOFF412 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS03 ∷ Toff412 ∷ []) (Toff412 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (Toff413 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Toff423 ∷ Sw12 ∷ []) (wl0084 c4) ▸
       at 2 2 (Toff423 ∷ CS01 ∷ []) (c₂ (CS) (Toffᵗ)) ▸
       at 1 2 (Toff413 ∷ Sw12 ∷ []) (wl0085 c4) ▸
       at 1 1 (Sw23 ∷ Toff412 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0003 c4) ▸ done

  b1 : Chain (Toff412 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (Toff412 ∷ CS03 ∷ [])
  b1 = at 1 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp TOFF403 at 1: 2 steps
lem-resp-TOFF403-at-1 : WsL → ⟪ (Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Toff413 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-TOFF403-at-1 c4 = run b0
  where
  b0 : Chain (Toff403 ∷ []) (Sw01 ∷ Toff413 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 0 2 (Sw01 ∷ Toff413 ∷ []) (lem-comm-push-TOFF403-sw0-L c4) ▸ done


-- comm TOFF412 CSd03: 9 steps
lem-comm-TOFF412-CSd03 : WsL → ⟪ (Toff412 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ Toff412 ∷ []) ⟫ʷ
lem-comm-TOFF412-CSd03 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff412 ∷ CS03⁻ ∷ []) (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Toff412 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (Toff413 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw12 ∷ Toff423 ∷ []) (sym (wl0085 c4)) ▸
       at 2 2 (CS01⁻ ∷ Toff423 ∷ []) (sym (c₂ (CS • CS • CS) (Toffᵗ))) ▸
       at 3 2 (Sw12 ∷ Toff413 ∷ []) (sym (wl0084 c4)) ▸
       at 4 1 (Sw23 ∷ Toff412 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0003 c4) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Toff412 ∷ []) (CS03⁻ ∷ Toff412 ∷ [])
  b1 = at 0 5 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CSd12 TOFF403: 15 steps
lem-comm-CSd12-TOFF403 : WsL → ⟪ (CS12⁻ ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CS12⁻ ∷ []) ⟫ʷ
lem-comm-CSd12-TOFF403 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS12⁻ ∷ Toff403 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ CS34⁻ ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw12 ∷ CS23⁻ ∷ []) (wl0028 c4) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw23 ∷ CS34⁻ ∷ []) (wl0012 c4) ▸
       at 4 2 (Toff201 ∷ CS34⁻ ∷ []) (sym (c₃ (Toffᵗ) (CS • CS • CS))) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ CS34⁻ ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Toff403 ∷ CS12⁻ ∷ [])
  b1 = at 5 2 (Sw23 ∷ CS24⁻ ∷ []) (wl0009 c4) ▸
       at 6 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0004 c4) ▸
       at 7 2 (Sw12 ∷ CS13⁻ ∷ []) (wl0029 c4) ▸
       at 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (wl0003 c4) ▸
       at 0 9 (Toff403 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CSd03 CCZ124: 9 steps
lem-comm-CSd03-CCZ124 : WsL → ⟪ (CS03⁻ ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-comm-CSd03-CCZ124 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS03⁻ ∷ CCZ124 ∷ []) (CCZ124 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0044 c4)) ▸
       at 2 2 (CCZ234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CCZ)) ▸
       at 1 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 1 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0003 c4) ▸ done

  b1 : Chain (CCZ124 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) (CCZ124 ∷ CS03⁻ ∷ [])
  b1 = at 1 5 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CS03 CCZ124: 9 steps
lem-comm-CS03-CCZ124 : WsL → ⟪ (CS03 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CS03 ∷ []) ⟫ʷ
lem-comm-CS03-CCZ124 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS03 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0044 c4)) ▸
       at 2 2 (CCZ234 ∷ CS01 ∷ []) (c₂ (CS) (CCZ)) ▸
       at 1 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 1 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0003 c4) ▸ done

  b1 : Chain (CCZ124 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (CCZ124 ∷ CS03 ∷ [])
  b1 = at 1 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp TOFF412 at 3: 7 steps
lem-resp-TOFF412-at-3 : WsL → ⟪ (Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff423 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-TOFF412-at-3 c4 = run b0
  where
  b0 : Chain (Toff412 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff423 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (Toff413 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 1 2 (Sw12 ∷ Toff423 ∷ []) (sym (wl0085 c4)) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 2 2 (Sw01 ∷ Toff423 ∷ []) (sym (c₂ (Swap) (Toffᵗ))) ▸ done


-- comm CZ03 TOFF412: 9 steps
lem-comm-CZ03-TOFF412 : WsL → ⟪ (CZ03 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CZ03 ∷ []) ⟫ʷ
lem-comm-CZ03-TOFF412 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CZ03 ∷ Toff412 ∷ []) (Toff412 ∷ Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (Toff413 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Toff423 ∷ Sw12 ∷ []) (wl0084 c4) ▸
       at 2 2 (Toff423 ∷ CZ01 ∷ []) (c₂ (CZ) (Toffᵗ)) ▸
       at 1 2 (Toff413 ∷ Sw12 ∷ []) (wl0085 c4) ▸
       at 1 1 (Sw23 ∷ Toff412 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0003 c4) ▸ done

  b1 : Chain (Toff412 ∷ Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ []) (Toff412 ∷ CZ03 ∷ [])
  b1 = at 1 5 (CZ03 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CSd03 TOFF412: 9 steps
lem-comm-CSd03-TOFF412 : WsL → ⟪ (CS03⁻ ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-comm-CSd03-TOFF412 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS03⁻ ∷ Toff412 ∷ []) (Toff412 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (Toff413 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Toff423 ∷ Sw12 ∷ []) (wl0084 c4) ▸
       at 2 2 (Toff423 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (Toffᵗ)) ▸
       at 1 2 (Toff413 ∷ Sw12 ∷ []) (wl0085 c4) ▸
       at 1 1 (Sw23 ∷ Toff412 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0003 c4) ▸ done

  b1 : Chain (Toff412 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) (Toff412 ∷ CS03⁻ ∷ [])
  b1 = at 1 5 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸ done


-- resp TOFF124 at 3: 7 steps
lem-resp-TOFF124-at-3 : WsL → ⟪ (Toff124 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff234 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-TOFF124-at-3 c4 = run b0
  where
  b0 : Chain (Toff124 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff234 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (Toff134 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 1 2 (Sw12 ∷ Toff234 ∷ []) (sym (wl0054 c4)) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 2 2 (Sw01 ∷ Toff234 ∷ []) (sym (c₂ (Swap) (Toff))) ▸ done


-- comm SWAP02 BOX(4;13): 9 steps
lem-comm-SWAP02-BOX⟨4·13⟩ : WsL → ⟪ (Sw02 ∷ Bx4-13 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-13 ∷ Sw02 ∷ []) ⟫ʷ
lem-comm-SWAP02-BOX⟨4·13⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw02 ∷ Bx4-13 ∷ []) (CZ13 ∷ Sw02 ∷ [])
  b0 = at 1 1 (CZ13 ∷ []) (refl) ▸
       at 1 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (Sw03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (CZ12 ∷ Sw03 ∷ []) (sym (wl0086 c4)) ▸
       at 2 1 (Sw23 ∷ Sw02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0003 c4) ▸
       at 0 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (CZ13 ∷ Sw02 ∷ []) (Bx4-13 ∷ Sw02 ∷ [])
  b1 = at 0 1 (Bx4-13 ∷ []) (refl) ▸ done


-- comm CZ04 TOFF312: 13 steps
lem-comm-CZ04-TOFF312 : WsL → ⟪ (CZ04 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CZ04 ∷ []) ⟫ʷ
lem-comm-CZ04-TOFF312 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CZ04 ∷ Toff312 ∷ []) (Sw34 ∷ Sw23 ∷ Toff413 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 6 3 (Toff412 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 5 3 (Toff413 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Toff423 ∷ Sw12 ∷ []) (wl0084 c4) ▸
       at 3 2 (Toff423 ∷ CZ01 ∷ []) (c₂ (CZ) (Toffᵗ)) ▸
       at 2 2 (Toff413 ∷ Sw12 ∷ []) (wl0085 c4) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Toff413 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (Toff312 ∷ CZ04 ∷ [])
  b1 = at 2 1 (Sw23 ∷ Toff412 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0003 c4) ▸
       at 1 1 (Sw34 ∷ Toff312 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0004 c4) ▸
       at 1 7 (CZ04 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm TOFF312 CSd04: 13 steps
lem-comm-TOFF312-CSd04 : WsL → ⟪ (Toff312 ∷ CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS04⁻ ∷ Toff312 ∷ []) ⟫ʷ
lem-comm-TOFF312-CSd04 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff312 ∷ CS04⁻ ∷ []) (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Toff413 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 3 (Toff412 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 2 3 (Toff413 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw12 ∷ Toff423 ∷ []) (sym (wl0085 c4)) ▸
       at 3 2 (CS01⁻ ∷ Toff423 ∷ []) (sym (c₂ (CS • CS • CS) (Toffᵗ))) ▸
       at 4 2 (Sw12 ∷ Toff413 ∷ []) (sym (wl0084 c4)) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Toff413 ∷ Sw23 ∷ Sw34 ∷ []) (CS04⁻ ∷ Toff312 ∷ [])
  b1 = at 5 1 (Sw23 ∷ Toff412 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0003 c4) ▸
       at 6 1 (Sw34 ∷ Toff312 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0004 c4) ▸
       at 0 7 (CS04⁻ ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CSd12 TOFF304: 15 steps
lem-comm-CSd12-TOFF304 : WsL → ⟪ (CS12⁻ ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CS12⁻ ∷ []) ⟫ʷ
lem-comm-CSd12-TOFF304 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS12⁻ ∷ Toff304 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ CS34⁻ ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw12 ∷ CS23⁻ ∷ []) (wl0028 c4) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw23 ∷ CS34⁻ ∷ []) (wl0012 c4) ▸
       at 4 2 (Toff102 ∷ CS34⁻ ∷ []) (sym (c₃ (K ↑ • CCZ • K ↑ • iI) (CS • CS • CS))) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ CS34⁻ ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Toff304 ∷ CS12⁻ ∷ [])
  b1 = at 5 2 (Sw23 ∷ CS24⁻ ∷ []) (wl0009 c4) ▸
       at 6 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0004 c4) ▸
       at 7 2 (Sw12 ∷ CS13⁻ ∷ []) (wl0029 c4) ▸
       at 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (wl0003 c4) ▸
       at 0 9 (Toff304 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm TOFF304 CSd12: 15 steps
lem-comm-TOFF304-CSd12 : WsL → ⟪ (Toff304 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ Toff304 ∷ []) ⟫ʷ
lem-comm-TOFF304-CSd12 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff304 ∷ CS12⁻ ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CS34⁻ ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 8 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CS23⁻ ∷ Sw12 ∷ []) (sym (wl0029 c4)) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 6 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0009 c4)) ▸
       at 4 2 (CS34⁻ ∷ Toff102 ∷ []) (c₃ (K ↑ • CCZ • K ↑ • iI) (CS • CS • CS)) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CS34⁻ ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (CS12⁻ ∷ Toff304 ∷ [])
  b1 = at 3 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0012 c4)) ▸
       at 3 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0004 c4) ▸
       at 1 2 (CS13⁻ ∷ Sw12 ∷ []) (sym (wl0028 c4)) ▸
       at 1 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0003 c4) ▸
       at 1 9 (Toff304 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CX40 CCZ123: 13 steps
lem-comm-CX40-CCZ123 : WsL → ⟪ (CX40 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CX40 ∷ []) ⟫ʷ
lem-comm-CX40-CCZ123 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX40 ∷ CCZ123 ∷ []) (Sw34 ∷ Sw23 ∷ CCZ134 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 6 3 (CCZ124 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 5 3 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0044 c4)) ▸
       at 3 2 (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ)) ▸
       at 2 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ CCZ134 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (CCZ123 ∷ CX40 ∷ [])
  b1 = at 2 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0003 c4) ▸
       at 1 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0004 c4) ▸
       at 1 7 (CX40 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CSd04 TOFF312: 13 steps
lem-comm-CSd04-TOFF312 : WsL → ⟪ (CS04⁻ ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CS04⁻ ∷ []) ⟫ʷ
lem-comm-CSd04-TOFF312 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS04⁻ ∷ Toff312 ∷ []) (Sw34 ∷ Sw23 ∷ Toff413 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 6 3 (Toff412 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 5 3 (Toff413 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Toff423 ∷ Sw12 ∷ []) (wl0084 c4) ▸
       at 3 2 (Toff423 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (Toffᵗ)) ▸
       at 2 2 (Toff413 ∷ Sw12 ∷ []) (wl0085 c4) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Toff413 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (Toff312 ∷ CS04⁻ ∷ [])
  b1 = at 2 1 (Sw23 ∷ Toff412 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0003 c4) ▸
       at 1 1 (Sw34 ∷ Toff312 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0004 c4) ▸
       at 1 7 (CS04⁻ ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CX40 at 2: 4 steps
lem-resp-CX40-at-2 : WsL → ⟪ (CX40 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CX41 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CX40-at-2 c4 = run b0
  where
  b0 : Chain (CX40 ∷ []) (Sw12 ∷ Sw01 ∷ CX41 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 0 2 (Sw12 ∷ CX40 ∷ []) (lem-comm-push-CX40-sw1-L c4) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 1 2 (Sw01 ∷ CX41 ∷ []) (lem-comm-push-CX40-sw0-L c4) ▸ done


-- comm CX40 TOFF312: 13 steps
lem-comm-CX40-TOFF312 : WsL → ⟪ (CX40 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CX40 ∷ []) ⟫ʷ
lem-comm-CX40-TOFF312 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX40 ∷ Toff312 ∷ []) (Sw34 ∷ Sw23 ∷ Toff413 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 6 3 (Toff412 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 5 3 (Toff413 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Toff423 ∷ Sw12 ∷ []) (wl0084 c4) ▸
       at 3 2 (Toff423 ∷ CX10 ∷ []) (c₂ (CX₁₀) (Toffᵗ)) ▸
       at 2 2 (Toff413 ∷ Sw12 ∷ []) (wl0085 c4) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Toff413 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (Toff312 ∷ CX40 ∷ [])
  b1 = at 2 1 (Sw23 ∷ Toff412 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0003 c4) ▸
       at 1 1 (Sw34 ∷ Toff312 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0004 c4) ▸
       at 1 7 (CX40 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CZ12 TOFF304: 15 steps
lem-comm-CZ12-TOFF304 : WsL → ⟪ (CZ12 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CZ12 ∷ []) ⟫ʷ
lem-comm-CZ12-TOFF304 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CZ12 ∷ Toff304 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ CZ34 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw12 ∷ CZ23 ∷ []) (wl0033 c4) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (CZ24 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw23 ∷ CZ34 ∷ []) (wl0034 c4) ▸
       at 4 2 (Toff102 ∷ CZ34 ∷ []) (sym (c₃ (K ↑ • CCZ • K ↑ • iI) (CZ))) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ CZ34 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Toff304 ∷ CZ12 ∷ [])
  b1 = at 5 2 (Sw23 ∷ CZ24 ∷ []) (wl0035 c4) ▸
       at 6 1 (Sw34 ∷ CZ23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0004 c4) ▸
       at 7 2 (Sw12 ∷ CZ13 ∷ []) (wl0036 c4) ▸
       at 8 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (wl0003 c4) ▸
       at 0 9 (Toff304 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CSd23 TOFF401: 9 steps
lem-comm-CSd23-TOFF401 : WsL → ⟪ (CS23⁻ ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ CS23⁻ ∷ []) ⟫ʷ
lem-comm-CSd23-TOFF401 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS23⁻ ∷ Toff401 ∷ []) (Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ CS23⁻ ∷ [])
  b0 = at 1 1 (Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw23 ∷ CS34⁻ ∷ []) (wl0012 c4) ▸
       at 2 2 (Toff201 ∷ CS34⁻ ∷ []) (sym (c₃ (Toffᵗ) (CS • CS • CS))) ▸
       at 3 2 (Sw23 ∷ CS24⁻ ∷ []) (wl0009 c4) ▸
       at 4 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0004 c4) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ CS23⁻ ∷ []) (Toff401 ∷ CS23⁻ ∷ [])
  b1 = at 0 5 (Toff401 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CS23 TOFF401: 9 steps
lem-comm-CS23-TOFF401 : WsL → ⟪ (CS23 ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ CS23 ∷ []) ⟫ʷ
lem-comm-CS23-TOFF401 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS23 ∷ Toff401 ∷ []) (Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ CS23 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 3 (CS24 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw23 ∷ CS34 ∷ []) (wl0011 c4) ▸
       at 2 2 (Toff201 ∷ CS34 ∷ []) (sym (c₃ (Toffᵗ) (CS))) ▸
       at 3 2 (Sw23 ∷ CS24 ∷ []) (wl0008 c4) ▸
       at 4 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0004 c4) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ CS23 ∷ []) (Toff401 ∷ CS23 ∷ [])
  b1 = at 0 5 (Toff401 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CSd24 TOFF301: 5 steps
lem-comm-CSd24-TOFF301 : WsL → ⟪ (CS24⁻ ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CS24⁻ ∷ []) ⟫ʷ
lem-comm-CSd24-TOFF301 c4 = run b0
  where
  b0 : Chain (CS24⁻ ∷ Toff301 ∷ []) (Toff301 ∷ CS24⁻ ∷ [])
  b0 = at 1 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ CS34⁻ ∷ []) (wl0012 c4) ▸
       at 1 2 (Toff201 ∷ CS34⁻ ∷ []) (sym (c₃ (Toffᵗ) (CS • CS • CS))) ▸
       at 2 2 (Sw23 ∷ CS24⁻ ∷ []) (wl0009 c4) ▸
       at 0 3 (Toff301 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CS24 TOFF301: 5 steps
lem-comm-CS24-TOFF301 : WsL → ⟪ (CS24 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CS24 ∷ []) ⟫ʷ
lem-comm-CS24-TOFF301 c4 = run b0
  where
  b0 : Chain (CS24 ∷ Toff301 ∷ []) (Toff301 ∷ CS24 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ CS34 ∷ []) (wl0011 c4) ▸
       at 1 2 (Toff201 ∷ CS34 ∷ []) (sym (c₃ (Toffᵗ) (CS))) ▸
       at 2 2 (Sw23 ∷ CS24 ∷ []) (wl0008 c4) ▸
       at 0 3 (Toff301 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm SWAP02 BOX(3;14): 11 steps
lem-comm-SWAP02-BOX⟨3·14⟩ : WsL → ⟪ (Sw02 ∷ Bx3-14 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-14 ∷ Sw02 ∷ []) ⟫ʷ
lem-comm-SWAP02-BOX⟨3·14⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw02 ∷ Bx3-14 ∷ []) (Sw34 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ Sw02 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ14 ∷ []) (refl) ▸
       at 1 1 (Sw34 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw34 ∷ Sw02 ∷ []) (c₃ (Swap ↑ • Swap • Swap ↑) (Swap)) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 2 3 (Sw03 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CZ12 ∷ Sw03 ∷ []) (sym (wl0086 c4)) ▸
       at 3 1 (Sw23 ∷ Sw02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0003 c4) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ Sw02 ∷ Sw34 ∷ []) (Bx3-14 ∷ Sw02 ∷ [])
  b1 = at 4 2 (Sw34 ∷ Sw02 ∷ []) (c₃ (Swap ↑ • Swap • Swap ↑) (Swap)) ▸
       at 0 5 (CZ14 ∷ []) (by-assoc Eq.refl) ▸
       at 0 1 (Bx3-14 ∷ []) (refl) ▸ done


-- comm CZ12 TOFF403: 15 steps
lem-comm-CZ12-TOFF403 : WsL → ⟪ (CZ12 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CZ12 ∷ []) ⟫ʷ
lem-comm-CZ12-TOFF403 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CZ12 ∷ Toff403 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ CZ34 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw12 ∷ CZ23 ∷ []) (wl0033 c4) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (CZ24 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw23 ∷ CZ34 ∷ []) (wl0034 c4) ▸
       at 4 2 (Toff201 ∷ CZ34 ∷ []) (sym (c₃ (Toffᵗ) (CZ))) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ CZ34 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Toff403 ∷ CZ12 ∷ [])
  b1 = at 5 2 (Sw23 ∷ CZ24 ∷ []) (wl0035 c4) ▸
       at 6 1 (Sw34 ∷ CZ23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0004 c4) ▸
       at 7 2 (Sw12 ∷ CZ13 ∷ []) (wl0036 c4) ▸
       at 8 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (wl0003 c4) ▸
       at 0 9 (Toff403 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CS04 TOFF312: 13 steps
lem-comm-CS04-TOFF312 : WsL → ⟪ (CS04 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CS04 ∷ []) ⟫ʷ
lem-comm-CS04-TOFF312 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS04 ∷ Toff312 ∷ []) (Sw34 ∷ Sw23 ∷ Toff413 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 6 3 (Toff412 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 5 3 (Toff413 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Toff423 ∷ Sw12 ∷ []) (wl0084 c4) ▸
       at 3 2 (Toff423 ∷ CS01 ∷ []) (c₂ (CS) (Toffᵗ)) ▸
       at 2 2 (Toff413 ∷ Sw12 ∷ []) (wl0085 c4) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Toff413 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (Toff312 ∷ CS04 ∷ [])
  b1 = at 2 1 (Sw23 ∷ Toff412 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0003 c4) ▸
       at 1 1 (Sw34 ∷ Toff312 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0004 c4) ▸
       at 1 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm TOFF312 CS04: 13 steps
lem-comm-TOFF312-CS04 : WsL → ⟪ (Toff312 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ Toff312 ∷ []) ⟫ʷ
lem-comm-TOFF312-CS04 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff312 ∷ CS04 ∷ []) (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Toff413 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 3 (Toff412 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 2 3 (Toff413 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw12 ∷ Toff423 ∷ []) (sym (wl0085 c4)) ▸
       at 3 2 (CS01 ∷ Toff423 ∷ []) (sym (c₂ (CS) (Toffᵗ))) ▸
       at 4 2 (Sw12 ∷ Toff413 ∷ []) (sym (wl0084 c4)) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Toff413 ∷ Sw23 ∷ Sw34 ∷ []) (CS04 ∷ Toff312 ∷ [])
  b1 = at 5 1 (Sw23 ∷ Toff412 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0003 c4) ▸
       at 6 1 (Sw34 ∷ Toff312 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0004 c4) ▸
       at 0 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CK41 at 2: 4 steps
lem-resp-CK41-at-2 : WsL → ⟪ (CK41 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CK42 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CK41-at-2 c4 = run b0
  where
  b0 : Chain (CK41 ∷ []) (Sw12 ∷ Sw01 ∷ CK42 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 0 2 (Sw12 ∷ CK42 ∷ []) (wl0087 c4) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 1 2 (Sw01 ∷ CK42 ∷ []) (sym (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑))) ▸ done


-- comm CS04 TOFF213: 13 steps
lem-comm-CS04-TOFF213 : WsL → ⟪ (CS04 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CS04 ∷ []) ⟫ʷ
lem-comm-CS04-TOFF213 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS04 ∷ Toff213 ∷ []) (Sw34 ∷ Sw23 ∷ Toff314 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 6 3 (Toff214 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 5 3 (Toff314 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Toff324 ∷ Sw12 ∷ []) (wl0045 c4) ▸
       at 3 2 (Toff324 ∷ CS01 ∷ []) (c₂ (CS) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 2 2 (Toff314 ∷ Sw12 ∷ []) (wl0038 c4) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Toff314 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (Toff213 ∷ CS04 ∷ [])
  b1 = at 2 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0003 c4) ▸
       at 1 1 (Sw34 ∷ Toff213 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0004 c4) ▸
       at 1 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CSd14 CCZ023: 7 steps
lem-comm-CSd14-CCZ023 : WsL → ⟪ (CS14⁻ ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ CS14⁻ ∷ []) ⟫ʷ
lem-comm-CSd14-CCZ023 c4 = run b0
  where
  b0 : Chain (CS14⁻ ∷ CCZ023 ∷ []) (CCZ023 ∷ CS14⁻ ∷ [])
  b0 = at 1 1 (Sw12 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ CS24⁻ ∷ []) (wl0014 c4) ▸
       at 1 2 (Sw23 ∷ CS34⁻ ∷ []) (wl0012 c4) ▸
       at 2 2 (CCZ012 ∷ CS34⁻ ∷ []) (sym (c₃ (CCZ) (CS • CS • CS))) ▸
       at 3 2 (Sw23 ∷ CS24⁻ ∷ []) (wl0009 c4) ▸
       at 4 2 (Sw12 ∷ CS14⁻ ∷ []) (wl0007 c4) ▸
       at 0 5 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CS14 CCZ023: 7 steps
lem-comm-CS14-CCZ023 : WsL → ⟪ (CS14 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ CS14 ∷ []) ⟫ʷ
lem-comm-CS14-CCZ023 c4 = run b0
  where
  b0 : Chain (CS14 ∷ CCZ023 ∷ []) (CCZ023 ∷ CS14 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ CS24 ∷ []) (wl0013 c4) ▸
       at 1 2 (Sw23 ∷ CS34 ∷ []) (wl0011 c4) ▸
       at 2 2 (CCZ012 ∷ CS34 ∷ []) (sym (c₃ (CCZ) (CS))) ▸
       at 3 2 (Sw23 ∷ CS24 ∷ []) (wl0008 c4) ▸
       at 4 2 (Sw12 ∷ CS14 ∷ []) (wl0005 c4) ▸
       at 0 5 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm push CK40 sw1 L: 5 steps
lem-comm-push-CK40-sw1-L : WsL → ⟪ (CK40 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CK40 ∷ []) ⟫ʷ
lem-comm-push-CK40-sw1-L c4 = run b0
  where
  b0 : Chain (CK40 ∷ Sw12 ∷ []) (Sw12 ∷ CK40 ∷ [])
  b0 = at 0 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 1 2 (Sw12 ∷ CK30 ∷ []) (wl0088 c4) ▸
       at 0 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 1 3 (CK40 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CK40 at 2: 4 steps
lem-resp-CK40-at-2 : WsL → ⟪ (CK40 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CK41 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CK40-at-2 c4 = run b0
  where
  b0 : Chain (CK40 ∷ []) (Sw12 ∷ Sw01 ∷ CK41 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 0 2 (Sw12 ∷ CK40 ∷ []) (lem-comm-push-CK40-sw1-L c4) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 1 2 (Sw01 ∷ CK41 ∷ []) (lem-comm-push-CK40-sw0-L c4) ▸ done


-- comm CSd04 CCZ123: 13 steps
lem-comm-CSd04-CCZ123 : WsL → ⟪ (CS04⁻ ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CS04⁻ ∷ []) ⟫ʷ
lem-comm-CSd04-CCZ123 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS04⁻ ∷ CCZ123 ∷ []) (Sw34 ∷ Sw23 ∷ CCZ134 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 6 3 (CCZ124 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 5 3 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0044 c4)) ▸
       at 3 2 (CCZ234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CCZ)) ▸
       at 2 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ CCZ134 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (CCZ123 ∷ CS04⁻ ∷ [])
  b1 = at 2 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0003 c4) ▸
       at 1 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0004 c4) ▸
       at 1 7 (CS04⁻ ∷ []) (by-assoc Eq.refl) ▸ done


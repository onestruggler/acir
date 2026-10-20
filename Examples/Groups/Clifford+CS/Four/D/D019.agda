{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D019 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Tools using (ax)
open import Examples.Groups.Clifford+CS.TopWeakening using (low-comm)
open import Examples.Groups.Clifford+CS.Idle using (low₁-comm)
open import Examples.Groups.Clifford+CS.Four.Chain
open import Examples.Groups.Clifford+CS.Four.Wins.W01 using (wn00001 ; wn00003 ; wn00005 ; wn00007 ; wn00014 ; wn00024 ; wn00025 ; wn00027 ; wn00030 ; wn00031 ; wn00071 ; wn00072 ; wn00074 ; wn00122 ; wn00124 ; wn00127)
open import Examples.Groups.Clifford+CS.Four.Wins.W02 using (wn00334 ; wn00335 ; wn00336 ; wn00368 ; wn00385 ; wn00386 ; wn00387 ; wn00388 ; wn00389 ; wn00390 ; wn00391 ; wn00392 ; wn00393 ; wn00394 ; wn00395 ; wn00396 ; wn00397)

-- sw2 TOFF213: 15 steps
lem-sw2-TOFF213 : ⟪ (Sw23 ∷ Toff213 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ []) ⟫ʷ
lem-sw2-TOFF213 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw23 ∷ Toff213 ∷ Sw23 ∷ []) (K3 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ Sw23 ∷ CS13 ∷ K2 ∷ ι1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (K3 ∷ Sw23 ∷ []) wn00335 ▸
       at 1 2 (CS23 ∷ Sw23 ∷ []) wn00071 ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS23⁻ ∷ Sw23 ∷ []) wn00072 ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (K3 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ Sw23 ∷ CS13 ∷ K2 ∷ ι1 ∷ Sw23 ∷ []) (Toff312 ∷ [])
  b1 = at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 6 2 (K3 ∷ Sw23 ∷ []) wn00335 ▸
       at 7 2 (ι1 ∷ Sw23 ∷ []) (sym (low-comm ((iI ↑)) (Swap))) ▸
       at 0 8 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) wn00385 ▸
       at 0 8 (Toff312 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 TOFF301: 28 steps
lem-sw2-TOFF301 : ⟪ (Sw23 ∷ Toff301 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ []) ⟫ʷ
lem-sw2-TOFF301 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Sw23 ∷ Toff301 ∷ Sw23 ∷ []) (Sw23 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (K3 ∷ Sw23 ∷ []) wn00335 ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw23 ∷ []) (K2 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw23 ∷ [])
  b1 = at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K3 ∷ Sw23 ∷ []) wn00335 ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 9 2 [] wn00003 ▸
       at 0 2 (K2 ∷ Sw23 ∷ []) wn00336 ▸
       at 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (K2 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw23 ∷ []) (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ Sw23 ∷ ι ∷ Sw23 ∷ [])
  b2 = at 1 2 [] wn00003 ▸
       at 2 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 6 2 (K2 ∷ Sw23 ∷ []) wn00336 ▸ done

  b3 : Chain (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ Sw23 ∷ ι ∷ Sw23 ∷ []) (Toff201 ∷ [])
  b3 = at 7 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 0 8 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) wn00368 ▸
       at 0 8 (Toff201 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 TOFF302: 47 steps
lem-sw2-TOFF302 : ⟪ (Sw23 ∷ Toff302 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ []) ⟫ʷ
lem-sw2-TOFF302 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (run b5)))))
  where
  b0 : Chain (Sw23 ∷ Toff302 ∷ Sw23 ∷ []) (Sw23 ∷ K3 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ K3 ∷ ι1 ∷ Sw01 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw01 ∷ Toff312 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑))) ▸
       at 2 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 3 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 4 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 5 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ K3 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ K3 ∷ ι1 ∷ Sw01 ∷ Sw23 ∷ []) (K2 ∷ Sw23 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K3 ∷ ι ∷ Sw23 ∷ [])
  b1 = at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑))) ▸
       at 8 2 (ι ∷ Sw01 ∷ []) wn00122 ▸
       at 9 2 [] wn00031 ▸
       at 0 2 (K2 ∷ Sw23 ∷ []) wn00336 ▸ done

  b2 : Chain (K2 ∷ Sw23 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K3 ∷ ι ∷ Sw23 ∷ []) (K2 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ Sw23 ∷ K3 ∷ ι ∷ Sw23 ∷ [])
  b2 = at 1 2 (CS23 ∷ Sw23 ∷ []) wn00071 ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS23⁻ ∷ Sw23 ∷ []) wn00072 ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸ done

  b3 : Chain (K2 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ Sw23 ∷ K3 ∷ ι ∷ Sw23 ∷ []) (Sw01 ∷ K2 ∷ CS23 ∷ Sw23 ∷ CX12 ∷ Sw01 ∷ Sw23 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw23 ∷ [])
  b3 = at 6 2 (K2 ∷ Sw23 ∷ []) wn00336 ▸
       at 7 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 0 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 1 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 2 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 4 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 4 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸ done

  b4 : Chain (Sw01 ∷ K2 ∷ CS23 ∷ Sw23 ∷ CX12 ∷ Sw01 ∷ Sw23 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw23 ∷ []) (Sw01 ∷ K2 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ Sw01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw23 ∷ [])
  b4 = at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 3 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 6 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸ done

  b5 : Chain (Sw01 ∷ K2 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ Sw01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw23 ∷ []) (Toff203 ∷ [])
  b5 = at 6 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 7 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 8 2 (ι1 ∷ Sw01 ∷ []) wn00124 ▸
       at 1 8 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) wn00386 ▸
       at 1 8 (Toff213 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff203 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 TOFF312: 15 steps
lem-sw2-TOFF312 : ⟪ (Sw23 ∷ Toff312 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ []) ⟫ʷ
lem-sw2-TOFF312 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw23 ∷ Toff312 ∷ Sw23 ∷ []) (K2 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ Sw23 ∷ CS13 ∷ K3 ∷ ι1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (K2 ∷ Sw23 ∷ []) wn00336 ▸
       at 1 2 (CS23 ∷ Sw23 ∷ []) wn00071 ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS23⁻ ∷ Sw23 ∷ []) wn00072 ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (K2 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ Sw23 ∷ CS13 ∷ K3 ∷ ι1 ∷ Sw23 ∷ []) (Toff213 ∷ [])
  b1 = at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 6 2 (K2 ∷ Sw23 ∷ []) wn00336 ▸
       at 7 2 (ι1 ∷ Sw23 ∷ []) (sym (low-comm ((iI ↑)) (Swap))) ▸
       at 0 8 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) wn00386 ▸
       at 0 8 (Toff213 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00003 ▸ done

-- xx0: 1 steps
lem-xx0 : ⟪ (X0 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-xx0 = run b0
  where
  b0 : Chain (X0 ∷ X0 ∷ []) []
  b0 = at 0 2 [] wn00387 ▸ done

-- xc01: 1 steps
lem-xc01 : ⟪ (X0 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X0 ∷ []) ⟫ʷ
lem-xc01 = run b0
  where
  b0 : Chain (X0 ∷ X1 ∷ []) (X1 ∷ X0 ∷ [])
  b0 = at 0 2 (X1 ∷ X0 ∷ []) (low₁-comm (X) (X)) ▸ done

-- xc02: 1 steps
lem-xc02 : ⟪ (X0 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X0 ∷ []) ⟫ʷ
lem-xc02 = run b0
  where
  b0 : Chain (X0 ∷ X2 ∷ []) (X2 ∷ X0 ∷ [])
  b0 = at 0 2 (X2 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑))) ▸ done

-- xc03: 1 steps
lem-xc03 : ⟪ (X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ X0 ∷ []) ⟫ʷ
lem-xc03 = run b0
  where
  b0 : Chain (X0 ∷ X3 ∷ []) (X3 ∷ X0 ∷ [])
  b0 = at 0 2 (X3 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑ ↑))) ▸ done

-- xx1: 1 steps
lem-xx1 : ⟪ (X1 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-xx1 = run b0
  where
  b0 : Chain (X1 ∷ X1 ∷ []) []
  b0 = at 0 2 [] wn00388 ▸ done

-- xc10: 1 steps
lem-xc10 : ⟪ (X1 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ []) ⟫ʷ
lem-xc10 = run b0
  where
  b0 : Chain (X1 ∷ X0 ∷ []) (X0 ∷ X1 ∷ [])
  b0 = at 0 2 (X0 ∷ X1 ∷ []) (sym (low₁-comm (X) (X))) ▸ done

-- xc12: 1 steps
lem-xc12 : ⟪ (X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X1 ∷ []) ⟫ʷ
lem-xc12 = run b0
  where
  b0 : Chain (X1 ∷ X2 ∷ []) (X2 ∷ X1 ∷ [])
  b0 = at 0 2 (X2 ∷ X1 ∷ []) (low-comm ((X ↑)) (X)) ▸ done

-- xc13: 1 steps
lem-xc13 : ⟪ (X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ X1 ∷ []) ⟫ʷ
lem-xc13 = run b0
  where
  b0 : Chain (X1 ∷ X3 ∷ []) (X3 ∷ X1 ∷ [])
  b0 = at 0 2 (X3 ∷ X1 ∷ []) (low-comm ((X ↑)) ((X ↑))) ▸ done

-- xx2: 1 steps
lem-xx2 : ⟪ (X2 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-xx2 = run b0
  where
  b0 : Chain (X2 ∷ X2 ∷ []) []
  b0 = at 0 2 [] wn00389 ▸ done

-- xc20: 1 steps
lem-xc20 : ⟪ (X2 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ []) ⟫ʷ
lem-xc20 = run b0
  where
  b0 : Chain (X2 ∷ X0 ∷ []) (X0 ∷ X2 ∷ [])
  b0 = at 0 2 (X0 ∷ X2 ∷ []) (sym (low₁-comm (X) ((X ↑)))) ▸ done

-- xc21: 1 steps
lem-xc21 : ⟪ (X2 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ []) ⟫ʷ
lem-xc21 = run b0
  where
  b0 : Chain (X2 ∷ X1 ∷ []) (X1 ∷ X2 ∷ [])
  b0 = at 0 2 (X1 ∷ X2 ∷ []) (sym (low-comm ((X ↑)) (X))) ▸ done

-- xc23: 1 steps
lem-xc23 : ⟪ (X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ X2 ∷ []) ⟫ʷ
lem-xc23 = run b0
  where
  b0 : Chain (X2 ∷ X3 ∷ []) (X3 ∷ X2 ∷ [])
  b0 = at 0 2 (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X)) ▸ done

-- xx3: 1 steps
lem-xx3 : ⟪ (X3 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-xx3 = run b0
  where
  b0 : Chain (X3 ∷ X3 ∷ []) []
  b0 = at 0 2 [] wn00390 ▸ done

-- xc30: 1 steps
lem-xc30 : ⟪ (X3 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ []) ⟫ʷ
lem-xc30 = run b0
  where
  b0 : Chain (X3 ∷ X0 ∷ []) (X0 ∷ X3 ∷ [])
  b0 = at 0 2 (X0 ∷ X3 ∷ []) (sym (low₁-comm (X) ((X ↑ ↑)))) ▸ done

-- xc31: 1 steps
lem-xc31 : ⟪ (X3 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X3 ∷ []) ⟫ʷ
lem-xc31 = run b0
  where
  b0 : Chain (X3 ∷ X1 ∷ []) (X1 ∷ X3 ∷ [])
  b0 = at 0 2 (X1 ∷ X3 ∷ []) (sym (low-comm ((X ↑)) ((X ↑)))) ▸ done

-- xc32: 1 steps
lem-xc32 : ⟪ (X3 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ []) ⟫ʷ
lem-xc32 = run b0
  where
  b0 : Chain (X3 ∷ X2 ∷ []) (X2 ∷ X3 ∷ [])
  b0 = at 0 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸ done

-- swsw0: 1 steps
lem-swsw0 : ⟪ (Sw01 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-swsw0 = run b0
  where
  b0 : Chain (Sw01 ∷ Sw01 ∷ []) []
  b0 = at 0 2 [] wn00031 ▸ done

-- swsw1: 1 steps
lem-swsw1 : ⟪ (Sw12 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-swsw1 = run b0
  where
  b0 : Chain (Sw12 ∷ Sw12 ∷ []) []
  b0 = at 0 2 [] wn00014 ▸ done

-- swsw2: 1 steps
lem-swsw2 : ⟪ (Sw23 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-swsw2 = run b0
  where
  b0 : Chain (Sw23 ∷ Sw23 ∷ []) []
  b0 = at 0 2 [] wn00003 ▸ done

-- xt0 0000: 0 steps
lem-xt0-0000 : ⟪ (X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ []) ⟫ʷ
lem-xt0-0000 = refl

-- xs0 0000: 0 steps
lem-xs0-0000 : ⟪ (X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ []) ⟫ʷ
lem-xs0-0000 = refl

-- xt0 1000: 1 steps
lem-xt0-1000 : ⟪ (X0 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-xt0-1000 = run b0
  where
  b0 : Chain (X0 ∷ X0 ∷ []) []
  b0 = at 0 2 [] wn00387 ▸ done

-- xs0 1000: 1 steps
lem-xs0-1000 : ⟪ (X0 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-xs0-1000 = run b0
  where
  b0 : Chain (X0 ∷ X0 ∷ []) []
  b0 = at 0 2 [] wn00387 ▸ done

-- xt0 0100: 0 steps
lem-xt0-0100 : ⟪ (X0 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ []) ⟫ʷ
lem-xt0-0100 = refl

-- xs0 0100: 1 steps
lem-xs0-0100 : ⟪ (X1 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ []) ⟫ʷ
lem-xs0-0100 = run b0
  where
  b0 : Chain (X1 ∷ X0 ∷ []) (X0 ∷ X1 ∷ [])
  b0 = at 0 2 (X0 ∷ X1 ∷ []) (sym (low₁-comm (X) (X))) ▸ done

-- xt0 1100: 1 steps
lem-xt0-1100 : ⟪ (X0 ∷ X0 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ []) ⟫ʷ
lem-xt0-1100 = run b0
  where
  b0 : Chain (X0 ∷ X0 ∷ X1 ∷ []) (X1 ∷ [])
  b0 = at 0 2 [] wn00387 ▸ done

-- xs0 1100: 2 steps
lem-xs0-1100 : ⟪ (X0 ∷ X1 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ []) ⟫ʷ
lem-xs0-1100 = run b0
  where
  b0 : Chain (X0 ∷ X1 ∷ X0 ∷ []) (X1 ∷ [])
  b0 = at 1 2 (X0 ∷ X1 ∷ []) (sym (low₁-comm (X) (X))) ▸
       at 0 2 [] wn00387 ▸ done

-- xt0 0010: 0 steps
lem-xt0-0010 : ⟪ (X0 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ []) ⟫ʷ
lem-xt0-0010 = refl

-- xs0 0010: 1 steps
lem-xs0-0010 : ⟪ (X2 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ []) ⟫ʷ
lem-xs0-0010 = run b0
  where
  b0 : Chain (X2 ∷ X0 ∷ []) (X0 ∷ X2 ∷ [])
  b0 = at 0 2 (X0 ∷ X2 ∷ []) (sym (low₁-comm (X) ((X ↑)))) ▸ done

-- xt0 1010: 1 steps
lem-xt0-1010 : ⟪ (X0 ∷ X0 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ []) ⟫ʷ
lem-xt0-1010 = run b0
  where
  b0 : Chain (X0 ∷ X0 ∷ X2 ∷ []) (X2 ∷ [])
  b0 = at 0 2 [] wn00387 ▸ done

-- xs0 1010: 2 steps
lem-xs0-1010 : ⟪ (X0 ∷ X2 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ []) ⟫ʷ
lem-xs0-1010 = run b0
  where
  b0 : Chain (X0 ∷ X2 ∷ X0 ∷ []) (X2 ∷ [])
  b0 = at 1 2 (X0 ∷ X2 ∷ []) (sym (low₁-comm (X) ((X ↑)))) ▸
       at 0 2 [] wn00387 ▸ done

-- xt0 0110: 0 steps
lem-xt0-0110 : ⟪ (X0 ∷ X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X2 ∷ []) ⟫ʷ
lem-xt0-0110 = refl

-- xs0 0110: 2 steps
lem-xs0-0110 : ⟪ (X1 ∷ X2 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X2 ∷ []) ⟫ʷ
lem-xs0-0110 = run b0
  where
  b0 : Chain (X1 ∷ X2 ∷ X0 ∷ []) (X0 ∷ X1 ∷ X2 ∷ [])
  b0 = at 1 2 (X0 ∷ X2 ∷ []) (sym (low₁-comm (X) ((X ↑)))) ▸
       at 0 2 (X0 ∷ X1 ∷ []) (sym (low₁-comm (X) (X))) ▸ done

-- xt0 1110: 1 steps
lem-xt0-1110 : ⟪ (X0 ∷ X0 ∷ X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ []) ⟫ʷ
lem-xt0-1110 = run b0
  where
  b0 : Chain (X0 ∷ X0 ∷ X1 ∷ X2 ∷ []) (X1 ∷ X2 ∷ [])
  b0 = at 0 2 [] wn00387 ▸ done

-- xs0 1110: 3 steps
lem-xs0-1110 : ⟪ (X0 ∷ X1 ∷ X2 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ []) ⟫ʷ
lem-xs0-1110 = run b0
  where
  b0 : Chain (X0 ∷ X1 ∷ X2 ∷ X0 ∷ []) (X1 ∷ X2 ∷ [])
  b0 = at 2 2 (X0 ∷ X2 ∷ []) (sym (low₁-comm (X) ((X ↑)))) ▸
       at 1 2 (X0 ∷ X1 ∷ []) (sym (low₁-comm (X) (X))) ▸
       at 0 2 [] wn00387 ▸ done

-- xt0 0001: 0 steps
lem-xt0-0001 : ⟪ (X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ []) ⟫ʷ
lem-xt0-0001 = refl

-- xs0 0001: 1 steps
lem-xs0-0001 : ⟪ (X3 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ []) ⟫ʷ
lem-xs0-0001 = run b0
  where
  b0 : Chain (X3 ∷ X0 ∷ []) (X0 ∷ X3 ∷ [])
  b0 = at 0 2 (X0 ∷ X3 ∷ []) (sym (low₁-comm (X) ((X ↑ ↑)))) ▸ done

-- xt0 1001: 1 steps
lem-xt0-1001 : ⟪ (X0 ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ []) ⟫ʷ
lem-xt0-1001 = run b0
  where
  b0 : Chain (X0 ∷ X0 ∷ X3 ∷ []) (X3 ∷ [])
  b0 = at 0 2 [] wn00387 ▸ done

-- xs0 1001: 2 steps
lem-xs0-1001 : ⟪ (X0 ∷ X3 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ []) ⟫ʷ
lem-xs0-1001 = run b0
  where
  b0 : Chain (X0 ∷ X3 ∷ X0 ∷ []) (X3 ∷ [])
  b0 = at 1 2 (X0 ∷ X3 ∷ []) (sym (low₁-comm (X) ((X ↑ ↑)))) ▸
       at 0 2 [] wn00387 ▸ done

-- xt0 0101: 0 steps
lem-xt0-0101 : ⟪ (X0 ∷ X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X3 ∷ []) ⟫ʷ
lem-xt0-0101 = refl

-- xs0 0101: 2 steps
lem-xs0-0101 : ⟪ (X1 ∷ X3 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X3 ∷ []) ⟫ʷ
lem-xs0-0101 = run b0
  where
  b0 : Chain (X1 ∷ X3 ∷ X0 ∷ []) (X0 ∷ X1 ∷ X3 ∷ [])
  b0 = at 1 2 (X0 ∷ X3 ∷ []) (sym (low₁-comm (X) ((X ↑ ↑)))) ▸
       at 0 2 (X0 ∷ X1 ∷ []) (sym (low₁-comm (X) (X))) ▸ done

-- xt0 1101: 1 steps
lem-xt0-1101 : ⟪ (X0 ∷ X0 ∷ X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X3 ∷ []) ⟫ʷ
lem-xt0-1101 = run b0
  where
  b0 : Chain (X0 ∷ X0 ∷ X1 ∷ X3 ∷ []) (X1 ∷ X3 ∷ [])
  b0 = at 0 2 [] wn00387 ▸ done

-- xs0 1101: 3 steps
lem-xs0-1101 : ⟪ (X0 ∷ X1 ∷ X3 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X3 ∷ []) ⟫ʷ
lem-xs0-1101 = run b0
  where
  b0 : Chain (X0 ∷ X1 ∷ X3 ∷ X0 ∷ []) (X1 ∷ X3 ∷ [])
  b0 = at 2 2 (X0 ∷ X3 ∷ []) (sym (low₁-comm (X) ((X ↑ ↑)))) ▸
       at 1 2 (X0 ∷ X1 ∷ []) (sym (low₁-comm (X) (X))) ▸
       at 0 2 [] wn00387 ▸ done

-- xt0 0011: 0 steps
lem-xt0-0011 : ⟪ (X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xt0-0011 = refl

-- xs0 0011: 2 steps
lem-xs0-0011 : ⟪ (X2 ∷ X3 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xs0-0011 = run b0
  where
  b0 : Chain (X2 ∷ X3 ∷ X0 ∷ []) (X0 ∷ X2 ∷ X3 ∷ [])
  b0 = at 1 2 (X0 ∷ X3 ∷ []) (sym (low₁-comm (X) ((X ↑ ↑)))) ▸
       at 0 2 (X0 ∷ X2 ∷ []) (sym (low₁-comm (X) ((X ↑)))) ▸ done

-- xt0 1011: 1 steps
lem-xt0-1011 : ⟪ (X0 ∷ X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ []) ⟫ʷ
lem-xt0-1011 = run b0
  where
  b0 : Chain (X0 ∷ X0 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ [])
  b0 = at 0 2 [] wn00387 ▸ done

-- xs0 1011: 3 steps
lem-xs0-1011 : ⟪ (X0 ∷ X2 ∷ X3 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ []) ⟫ʷ
lem-xs0-1011 = run b0
  where
  b0 : Chain (X0 ∷ X2 ∷ X3 ∷ X0 ∷ []) (X2 ∷ X3 ∷ [])
  b0 = at 2 2 (X0 ∷ X3 ∷ []) (sym (low₁-comm (X) ((X ↑ ↑)))) ▸
       at 1 2 (X0 ∷ X2 ∷ []) (sym (low₁-comm (X) ((X ↑)))) ▸
       at 0 2 [] wn00387 ▸ done

-- xt0 0111: 0 steps
lem-xt0-0111 : ⟪ (X0 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xt0-0111 = refl

-- xs0 0111: 3 steps
lem-xs0-0111 : ⟪ (X1 ∷ X2 ∷ X3 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xs0-0111 = run b0
  where
  b0 : Chain (X1 ∷ X2 ∷ X3 ∷ X0 ∷ []) (X0 ∷ X1 ∷ X2 ∷ X3 ∷ [])
  b0 = at 2 2 (X0 ∷ X3 ∷ []) (sym (low₁-comm (X) ((X ↑ ↑)))) ▸
       at 1 2 (X0 ∷ X2 ∷ []) (sym (low₁-comm (X) ((X ↑)))) ▸
       at 0 2 (X0 ∷ X1 ∷ []) (sym (low₁-comm (X) (X))) ▸ done

-- xt0 1111: 1 steps
lem-xt0-1111 : ⟪ (X0 ∷ X0 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xt0-1111 = run b0
  where
  b0 : Chain (X0 ∷ X0 ∷ X1 ∷ X2 ∷ X3 ∷ []) (X1 ∷ X2 ∷ X3 ∷ [])
  b0 = at 0 2 [] wn00387 ▸ done

-- xs0 1111: 4 steps
lem-xs0-1111 : ⟪ (X0 ∷ X1 ∷ X2 ∷ X3 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xs0-1111 = run b0
  where
  b0 : Chain (X0 ∷ X1 ∷ X2 ∷ X3 ∷ X0 ∷ []) (X1 ∷ X2 ∷ X3 ∷ [])
  b0 = at 3 2 (X0 ∷ X3 ∷ []) (sym (low₁-comm (X) ((X ↑ ↑)))) ▸
       at 2 2 (X0 ∷ X2 ∷ []) (sym (low₁-comm (X) ((X ↑)))) ▸
       at 1 2 (X0 ∷ X1 ∷ []) (sym (low₁-comm (X) (X))) ▸
       at 0 2 [] wn00387 ▸ done

-- xt1 0000: 0 steps
lem-xt1-0000 : ⟪ (X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ []) ⟫ʷ
lem-xt1-0000 = refl

-- xs1 0000: 0 steps
lem-xs1-0000 : ⟪ (X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ []) ⟫ʷ
lem-xs1-0000 = refl

-- xt1 1000: 1 steps
lem-xt1-1000 : ⟪ (X1 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ []) ⟫ʷ
lem-xt1-1000 = run b0
  where
  b0 : Chain (X1 ∷ X0 ∷ []) (X0 ∷ X1 ∷ [])
  b0 = at 0 2 (X0 ∷ X1 ∷ []) (sym (low₁-comm (X) (X))) ▸ done

-- xs1 1000: 0 steps
lem-xs1-1000 : ⟪ (X0 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ []) ⟫ʷ
lem-xs1-1000 = refl

-- xt1 0100: 1 steps
lem-xt1-0100 : ⟪ (X1 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-xt1-0100 = run b0
  where
  b0 : Chain (X1 ∷ X1 ∷ []) []
  b0 = at 0 2 [] wn00388 ▸ done

-- xs1 0100: 1 steps
lem-xs1-0100 : ⟪ (X1 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-xs1-0100 = run b0
  where
  b0 : Chain (X1 ∷ X1 ∷ []) []
  b0 = at 0 2 [] wn00388 ▸ done

-- xt1 1100: 2 steps
lem-xt1-1100 : ⟪ (X1 ∷ X0 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ []) ⟫ʷ
lem-xt1-1100 = run b0
  where
  b0 : Chain (X1 ∷ X0 ∷ X1 ∷ []) (X0 ∷ [])
  b0 = at 0 2 (X0 ∷ X1 ∷ []) (sym (low₁-comm (X) (X))) ▸
       at 1 2 [] wn00388 ▸ done

-- xs1 1100: 1 steps
lem-xs1-1100 : ⟪ (X0 ∷ X1 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ []) ⟫ʷ
lem-xs1-1100 = run b0
  where
  b0 : Chain (X0 ∷ X1 ∷ X1 ∷ []) (X0 ∷ [])
  b0 = at 1 2 [] wn00388 ▸ done

-- xt1 0010: 0 steps
lem-xt1-0010 : ⟪ (X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ []) ⟫ʷ
lem-xt1-0010 = refl

-- xs1 0010: 1 steps
lem-xs1-0010 : ⟪ (X2 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ []) ⟫ʷ
lem-xs1-0010 = run b0
  where
  b0 : Chain (X2 ∷ X1 ∷ []) (X1 ∷ X2 ∷ [])
  b0 = at 0 2 (X1 ∷ X2 ∷ []) (sym (low-comm ((X ↑)) (X))) ▸ done

-- xt1 1010: 1 steps
lem-xt1-1010 : ⟪ (X1 ∷ X0 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X2 ∷ []) ⟫ʷ
lem-xt1-1010 = run b0
  where
  b0 : Chain (X1 ∷ X0 ∷ X2 ∷ []) (X0 ∷ X1 ∷ X2 ∷ [])
  b0 = at 0 2 (X0 ∷ X1 ∷ []) (sym (low₁-comm (X) (X))) ▸ done

-- xs1 1010: 1 steps
lem-xs1-1010 : ⟪ (X0 ∷ X2 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X2 ∷ []) ⟫ʷ
lem-xs1-1010 = run b0
  where
  b0 : Chain (X0 ∷ X2 ∷ X1 ∷ []) (X0 ∷ X1 ∷ X2 ∷ [])
  b0 = at 1 2 (X1 ∷ X2 ∷ []) (sym (low-comm ((X ↑)) (X))) ▸ done

-- xt1 0110: 1 steps
lem-xt1-0110 : ⟪ (X1 ∷ X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ []) ⟫ʷ
lem-xt1-0110 = run b0
  where
  b0 : Chain (X1 ∷ X1 ∷ X2 ∷ []) (X2 ∷ [])
  b0 = at 0 2 [] wn00388 ▸ done

-- xs1 0110: 2 steps
lem-xs1-0110 : ⟪ (X1 ∷ X2 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ []) ⟫ʷ
lem-xs1-0110 = run b0
  where
  b0 : Chain (X1 ∷ X2 ∷ X1 ∷ []) (X2 ∷ [])
  b0 = at 1 2 (X1 ∷ X2 ∷ []) (sym (low-comm ((X ↑)) (X))) ▸
       at 0 2 [] wn00388 ▸ done

-- xt1 1110: 2 steps
lem-xt1-1110 : ⟪ (X1 ∷ X0 ∷ X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ []) ⟫ʷ
lem-xt1-1110 = run b0
  where
  b0 : Chain (X1 ∷ X0 ∷ X1 ∷ X2 ∷ []) (X0 ∷ X2 ∷ [])
  b0 = at 0 2 (X0 ∷ X1 ∷ []) (sym (low₁-comm (X) (X))) ▸
       at 1 2 [] wn00388 ▸ done

-- xs1 1110: 2 steps
lem-xs1-1110 : ⟪ (X0 ∷ X1 ∷ X2 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ []) ⟫ʷ
lem-xs1-1110 = run b0
  where
  b0 : Chain (X0 ∷ X1 ∷ X2 ∷ X1 ∷ []) (X0 ∷ X2 ∷ [])
  b0 = at 2 2 (X1 ∷ X2 ∷ []) (sym (low-comm ((X ↑)) (X))) ▸
       at 1 2 [] wn00388 ▸ done

-- xt1 0001: 0 steps
lem-xt1-0001 : ⟪ (X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X3 ∷ []) ⟫ʷ
lem-xt1-0001 = refl

-- xs1 0001: 1 steps
lem-xs1-0001 : ⟪ (X3 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X3 ∷ []) ⟫ʷ
lem-xs1-0001 = run b0
  where
  b0 : Chain (X3 ∷ X1 ∷ []) (X1 ∷ X3 ∷ [])
  b0 = at 0 2 (X1 ∷ X3 ∷ []) (sym (low-comm ((X ↑)) ((X ↑)))) ▸ done

-- xt1 1001: 1 steps
lem-xt1-1001 : ⟪ (X1 ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X3 ∷ []) ⟫ʷ
lem-xt1-1001 = run b0
  where
  b0 : Chain (X1 ∷ X0 ∷ X3 ∷ []) (X0 ∷ X1 ∷ X3 ∷ [])
  b0 = at 0 2 (X0 ∷ X1 ∷ []) (sym (low₁-comm (X) (X))) ▸ done

-- xs1 1001: 1 steps
lem-xs1-1001 : ⟪ (X0 ∷ X3 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X3 ∷ []) ⟫ʷ
lem-xs1-1001 = run b0
  where
  b0 : Chain (X0 ∷ X3 ∷ X1 ∷ []) (X0 ∷ X1 ∷ X3 ∷ [])
  b0 = at 1 2 (X1 ∷ X3 ∷ []) (sym (low-comm ((X ↑)) ((X ↑)))) ▸ done

-- xt1 0101: 1 steps
lem-xt1-0101 : ⟪ (X1 ∷ X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ []) ⟫ʷ
lem-xt1-0101 = run b0
  where
  b0 : Chain (X1 ∷ X1 ∷ X3 ∷ []) (X3 ∷ [])
  b0 = at 0 2 [] wn00388 ▸ done

-- xs1 0101: 2 steps
lem-xs1-0101 : ⟪ (X1 ∷ X3 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ []) ⟫ʷ
lem-xs1-0101 = run b0
  where
  b0 : Chain (X1 ∷ X3 ∷ X1 ∷ []) (X3 ∷ [])
  b0 = at 1 2 (X1 ∷ X3 ∷ []) (sym (low-comm ((X ↑)) ((X ↑)))) ▸
       at 0 2 [] wn00388 ▸ done

-- xt1 1101: 2 steps
lem-xt1-1101 : ⟪ (X1 ∷ X0 ∷ X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ []) ⟫ʷ
lem-xt1-1101 = run b0
  where
  b0 : Chain (X1 ∷ X0 ∷ X1 ∷ X3 ∷ []) (X0 ∷ X3 ∷ [])
  b0 = at 0 2 (X0 ∷ X1 ∷ []) (sym (low₁-comm (X) (X))) ▸
       at 1 2 [] wn00388 ▸ done

-- xs1 1101: 2 steps
lem-xs1-1101 : ⟪ (X0 ∷ X1 ∷ X3 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ []) ⟫ʷ
lem-xs1-1101 = run b0
  where
  b0 : Chain (X0 ∷ X1 ∷ X3 ∷ X1 ∷ []) (X0 ∷ X3 ∷ [])
  b0 = at 2 2 (X1 ∷ X3 ∷ []) (sym (low-comm ((X ↑)) ((X ↑)))) ▸
       at 1 2 [] wn00388 ▸ done

-- xt1 0011: 0 steps
lem-xt1-0011 : ⟪ (X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xt1-0011 = refl

-- xs1 0011: 2 steps
lem-xs1-0011 : ⟪ (X2 ∷ X3 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xs1-0011 = run b0
  where
  b0 : Chain (X2 ∷ X3 ∷ X1 ∷ []) (X1 ∷ X2 ∷ X3 ∷ [])
  b0 = at 1 2 (X1 ∷ X3 ∷ []) (sym (low-comm ((X ↑)) ((X ↑)))) ▸
       at 0 2 (X1 ∷ X2 ∷ []) (sym (low-comm ((X ↑)) (X))) ▸ done

-- xt1 1011: 1 steps
lem-xt1-1011 : ⟪ (X1 ∷ X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xt1-1011 = run b0
  where
  b0 : Chain (X1 ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X1 ∷ X2 ∷ X3 ∷ [])
  b0 = at 0 2 (X0 ∷ X1 ∷ []) (sym (low₁-comm (X) (X))) ▸ done

-- xs1 1011: 2 steps
lem-xs1-1011 : ⟪ (X0 ∷ X2 ∷ X3 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xs1-1011 = run b0
  where
  b0 : Chain (X0 ∷ X2 ∷ X3 ∷ X1 ∷ []) (X0 ∷ X1 ∷ X2 ∷ X3 ∷ [])
  b0 = at 2 2 (X1 ∷ X3 ∷ []) (sym (low-comm ((X ↑)) ((X ↑)))) ▸
       at 1 2 (X1 ∷ X2 ∷ []) (sym (low-comm ((X ↑)) (X))) ▸ done

-- xt1 0111: 1 steps
lem-xt1-0111 : ⟪ (X1 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ []) ⟫ʷ
lem-xt1-0111 = run b0
  where
  b0 : Chain (X1 ∷ X1 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ [])
  b0 = at 0 2 [] wn00388 ▸ done

-- xs1 0111: 3 steps
lem-xs1-0111 : ⟪ (X1 ∷ X2 ∷ X3 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ []) ⟫ʷ
lem-xs1-0111 = run b0
  where
  b0 : Chain (X1 ∷ X2 ∷ X3 ∷ X1 ∷ []) (X2 ∷ X3 ∷ [])
  b0 = at 2 2 (X1 ∷ X3 ∷ []) (sym (low-comm ((X ↑)) ((X ↑)))) ▸
       at 1 2 (X1 ∷ X2 ∷ []) (sym (low-comm ((X ↑)) (X))) ▸
       at 0 2 [] wn00388 ▸ done

-- xt1 1111: 2 steps
lem-xt1-1111 : ⟪ (X1 ∷ X0 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xt1-1111 = run b0
  where
  b0 : Chain (X1 ∷ X0 ∷ X1 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X2 ∷ X3 ∷ [])
  b0 = at 0 2 (X0 ∷ X1 ∷ []) (sym (low₁-comm (X) (X))) ▸
       at 1 2 [] wn00388 ▸ done

-- xs1 1111: 3 steps
lem-xs1-1111 : ⟪ (X0 ∷ X1 ∷ X2 ∷ X3 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xs1-1111 = run b0
  where
  b0 : Chain (X0 ∷ X1 ∷ X2 ∷ X3 ∷ X1 ∷ []) (X0 ∷ X2 ∷ X3 ∷ [])
  b0 = at 3 2 (X1 ∷ X3 ∷ []) (sym (low-comm ((X ↑)) ((X ↑)))) ▸
       at 2 2 (X1 ∷ X2 ∷ []) (sym (low-comm ((X ↑)) (X))) ▸
       at 1 2 [] wn00388 ▸ done

-- xt2 0000: 0 steps
lem-xt2-0000 : ⟪ (X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ []) ⟫ʷ
lem-xt2-0000 = refl

-- xs2 0000: 0 steps
lem-xs2-0000 : ⟪ (X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ []) ⟫ʷ
lem-xs2-0000 = refl

-- xt2 1000: 1 steps
lem-xt2-1000 : ⟪ (X2 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ []) ⟫ʷ
lem-xt2-1000 = run b0
  where
  b0 : Chain (X2 ∷ X0 ∷ []) (X0 ∷ X2 ∷ [])
  b0 = at 0 2 (X0 ∷ X2 ∷ []) (sym (low₁-comm (X) ((X ↑)))) ▸ done

-- xs2 1000: 0 steps
lem-xs2-1000 : ⟪ (X0 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ []) ⟫ʷ
lem-xs2-1000 = refl

-- xt2 0100: 1 steps
lem-xt2-0100 : ⟪ (X2 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ []) ⟫ʷ
lem-xt2-0100 = run b0
  where
  b0 : Chain (X2 ∷ X1 ∷ []) (X1 ∷ X2 ∷ [])
  b0 = at 0 2 (X1 ∷ X2 ∷ []) (sym (low-comm ((X ↑)) (X))) ▸ done

-- xs2 0100: 0 steps
lem-xs2-0100 : ⟪ (X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ []) ⟫ʷ
lem-xs2-0100 = refl

-- xt2 1100: 2 steps
lem-xt2-1100 : ⟪ (X2 ∷ X0 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X2 ∷ []) ⟫ʷ
lem-xt2-1100 = run b0
  where
  b0 : Chain (X2 ∷ X0 ∷ X1 ∷ []) (X0 ∷ X1 ∷ X2 ∷ [])
  b0 = at 0 2 (X0 ∷ X2 ∷ []) (sym (low₁-comm (X) ((X ↑)))) ▸
       at 1 2 (X1 ∷ X2 ∷ []) (sym (low-comm ((X ↑)) (X))) ▸ done

-- xs2 1100: 0 steps
lem-xs2-1100 : ⟪ (X0 ∷ X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X2 ∷ []) ⟫ʷ
lem-xs2-1100 = refl

-- xt2 0010: 1 steps
lem-xt2-0010 : ⟪ (X2 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-xt2-0010 = run b0
  where
  b0 : Chain (X2 ∷ X2 ∷ []) []
  b0 = at 0 2 [] wn00389 ▸ done

-- xs2 0010: 1 steps
lem-xs2-0010 : ⟪ (X2 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-xs2-0010 = run b0
  where
  b0 : Chain (X2 ∷ X2 ∷ []) []
  b0 = at 0 2 [] wn00389 ▸ done

-- xt2 1010: 2 steps
lem-xt2-1010 : ⟪ (X2 ∷ X0 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ []) ⟫ʷ
lem-xt2-1010 = run b0
  where
  b0 : Chain (X2 ∷ X0 ∷ X2 ∷ []) (X0 ∷ [])
  b0 = at 0 2 (X0 ∷ X2 ∷ []) (sym (low₁-comm (X) ((X ↑)))) ▸
       at 1 2 [] wn00389 ▸ done

-- xs2 1010: 1 steps
lem-xs2-1010 : ⟪ (X0 ∷ X2 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ []) ⟫ʷ
lem-xs2-1010 = run b0
  where
  b0 : Chain (X0 ∷ X2 ∷ X2 ∷ []) (X0 ∷ [])
  b0 = at 1 2 [] wn00389 ▸ done

-- xt2 0110: 2 steps
lem-xt2-0110 : ⟪ (X2 ∷ X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ []) ⟫ʷ
lem-xt2-0110 = run b0
  where
  b0 : Chain (X2 ∷ X1 ∷ X2 ∷ []) (X1 ∷ [])
  b0 = at 0 2 (X1 ∷ X2 ∷ []) (sym (low-comm ((X ↑)) (X))) ▸
       at 1 2 [] wn00389 ▸ done

-- xs2 0110: 1 steps
lem-xs2-0110 : ⟪ (X1 ∷ X2 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ []) ⟫ʷ
lem-xs2-0110 = run b0
  where
  b0 : Chain (X1 ∷ X2 ∷ X2 ∷ []) (X1 ∷ [])
  b0 = at 1 2 [] wn00389 ▸ done

-- xt2 1110: 3 steps
lem-xt2-1110 : ⟪ (X2 ∷ X0 ∷ X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ []) ⟫ʷ
lem-xt2-1110 = run b0
  where
  b0 : Chain (X2 ∷ X0 ∷ X1 ∷ X2 ∷ []) (X0 ∷ X1 ∷ [])
  b0 = at 0 2 (X0 ∷ X2 ∷ []) (sym (low₁-comm (X) ((X ↑)))) ▸
       at 1 2 (X1 ∷ X2 ∷ []) (sym (low-comm ((X ↑)) (X))) ▸
       at 2 2 [] wn00389 ▸ done

-- xs2 1110: 1 steps
lem-xs2-1110 : ⟪ (X0 ∷ X1 ∷ X2 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ []) ⟫ʷ
lem-xs2-1110 = run b0
  where
  b0 : Chain (X0 ∷ X1 ∷ X2 ∷ X2 ∷ []) (X0 ∷ X1 ∷ [])
  b0 = at 2 2 [] wn00389 ▸ done

-- xt2 0001: 0 steps
lem-xt2-0001 : ⟪ (X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ []) ⟫ʷ
lem-xt2-0001 = refl

-- xs2 0001: 1 steps
lem-xs2-0001 : ⟪ (X3 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ []) ⟫ʷ
lem-xs2-0001 = run b0
  where
  b0 : Chain (X3 ∷ X2 ∷ []) (X2 ∷ X3 ∷ [])
  b0 = at 0 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸ done

-- xt2 1001: 1 steps
lem-xt2-1001 : ⟪ (X2 ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xt2-1001 = run b0
  where
  b0 : Chain (X2 ∷ X0 ∷ X3 ∷ []) (X0 ∷ X2 ∷ X3 ∷ [])
  b0 = at 0 2 (X0 ∷ X2 ∷ []) (sym (low₁-comm (X) ((X ↑)))) ▸ done

-- xs2 1001: 1 steps
lem-xs2-1001 : ⟪ (X0 ∷ X3 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xs2-1001 = run b0
  where
  b0 : Chain (X0 ∷ X3 ∷ X2 ∷ []) (X0 ∷ X2 ∷ X3 ∷ [])
  b0 = at 1 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸ done

-- xt2 0101: 1 steps
lem-xt2-0101 : ⟪ (X2 ∷ X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xt2-0101 = run b0
  where
  b0 : Chain (X2 ∷ X1 ∷ X3 ∷ []) (X1 ∷ X2 ∷ X3 ∷ [])
  b0 = at 0 2 (X1 ∷ X2 ∷ []) (sym (low-comm ((X ↑)) (X))) ▸ done

-- xs2 0101: 1 steps
lem-xs2-0101 : ⟪ (X1 ∷ X3 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xs2-0101 = run b0
  where
  b0 : Chain (X1 ∷ X3 ∷ X2 ∷ []) (X1 ∷ X2 ∷ X3 ∷ [])
  b0 = at 1 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸ done

-- xt2 1101: 2 steps
lem-xt2-1101 : ⟪ (X2 ∷ X0 ∷ X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xt2-1101 = run b0
  where
  b0 : Chain (X2 ∷ X0 ∷ X1 ∷ X3 ∷ []) (X0 ∷ X1 ∷ X2 ∷ X3 ∷ [])
  b0 = at 0 2 (X0 ∷ X2 ∷ []) (sym (low₁-comm (X) ((X ↑)))) ▸
       at 1 2 (X1 ∷ X2 ∷ []) (sym (low-comm ((X ↑)) (X))) ▸ done

-- xs2 1101: 1 steps
lem-xs2-1101 : ⟪ (X0 ∷ X1 ∷ X3 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xs2-1101 = run b0
  where
  b0 : Chain (X0 ∷ X1 ∷ X3 ∷ X2 ∷ []) (X0 ∷ X1 ∷ X2 ∷ X3 ∷ [])
  b0 = at 2 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸ done

-- xt2 0011: 1 steps
lem-xt2-0011 : ⟪ (X2 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ []) ⟫ʷ
lem-xt2-0011 = run b0
  where
  b0 : Chain (X2 ∷ X2 ∷ X3 ∷ []) (X3 ∷ [])
  b0 = at 0 2 [] wn00389 ▸ done

-- xs2 0011: 2 steps
lem-xs2-0011 : ⟪ (X2 ∷ X3 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ []) ⟫ʷ
lem-xs2-0011 = run b0
  where
  b0 : Chain (X2 ∷ X3 ∷ X2 ∷ []) (X3 ∷ [])
  b0 = at 1 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸
       at 0 2 [] wn00389 ▸ done

-- xt2 1011: 2 steps
lem-xt2-1011 : ⟪ (X2 ∷ X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ []) ⟫ʷ
lem-xt2-1011 = run b0
  where
  b0 : Chain (X2 ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X3 ∷ [])
  b0 = at 0 2 (X0 ∷ X2 ∷ []) (sym (low₁-comm (X) ((X ↑)))) ▸
       at 1 2 [] wn00389 ▸ done

-- xs2 1011: 2 steps
lem-xs2-1011 : ⟪ (X0 ∷ X2 ∷ X3 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ []) ⟫ʷ
lem-xs2-1011 = run b0
  where
  b0 : Chain (X0 ∷ X2 ∷ X3 ∷ X2 ∷ []) (X0 ∷ X3 ∷ [])
  b0 = at 2 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸
       at 1 2 [] wn00389 ▸ done

-- xt2 0111: 2 steps
lem-xt2-0111 : ⟪ (X2 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X3 ∷ []) ⟫ʷ
lem-xt2-0111 = run b0
  where
  b0 : Chain (X2 ∷ X1 ∷ X2 ∷ X3 ∷ []) (X1 ∷ X3 ∷ [])
  b0 = at 0 2 (X1 ∷ X2 ∷ []) (sym (low-comm ((X ↑)) (X))) ▸
       at 1 2 [] wn00389 ▸ done

-- xs2 0111: 2 steps
lem-xs2-0111 : ⟪ (X1 ∷ X2 ∷ X3 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X3 ∷ []) ⟫ʷ
lem-xs2-0111 = run b0
  where
  b0 : Chain (X1 ∷ X2 ∷ X3 ∷ X2 ∷ []) (X1 ∷ X3 ∷ [])
  b0 = at 2 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸
       at 1 2 [] wn00389 ▸ done

-- xt2 1111: 3 steps
lem-xt2-1111 : ⟪ (X2 ∷ X0 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X3 ∷ []) ⟫ʷ
lem-xt2-1111 = run b0
  where
  b0 : Chain (X2 ∷ X0 ∷ X1 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X1 ∷ X3 ∷ [])
  b0 = at 0 2 (X0 ∷ X2 ∷ []) (sym (low₁-comm (X) ((X ↑)))) ▸
       at 1 2 (X1 ∷ X2 ∷ []) (sym (low-comm ((X ↑)) (X))) ▸
       at 2 2 [] wn00389 ▸ done

-- xs2 1111: 2 steps
lem-xs2-1111 : ⟪ (X0 ∷ X1 ∷ X2 ∷ X3 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X3 ∷ []) ⟫ʷ
lem-xs2-1111 = run b0
  where
  b0 : Chain (X0 ∷ X1 ∷ X2 ∷ X3 ∷ X2 ∷ []) (X0 ∷ X1 ∷ X3 ∷ [])
  b0 = at 3 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸
       at 2 2 [] wn00389 ▸ done

-- xt3 0000: 0 steps
lem-xt3-0000 : ⟪ (X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ []) ⟫ʷ
lem-xt3-0000 = refl

-- xs3 0000: 0 steps
lem-xs3-0000 : ⟪ (X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ []) ⟫ʷ
lem-xs3-0000 = refl

-- xt3 1000: 1 steps
lem-xt3-1000 : ⟪ (X3 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ []) ⟫ʷ
lem-xt3-1000 = run b0
  where
  b0 : Chain (X3 ∷ X0 ∷ []) (X0 ∷ X3 ∷ [])
  b0 = at 0 2 (X0 ∷ X3 ∷ []) (sym (low₁-comm (X) ((X ↑ ↑)))) ▸ done

-- xs3 1000: 0 steps
lem-xs3-1000 : ⟪ (X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ []) ⟫ʷ
lem-xs3-1000 = refl

-- xt3 0100: 1 steps
lem-xt3-0100 : ⟪ (X3 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X3 ∷ []) ⟫ʷ
lem-xt3-0100 = run b0
  where
  b0 : Chain (X3 ∷ X1 ∷ []) (X1 ∷ X3 ∷ [])
  b0 = at 0 2 (X1 ∷ X3 ∷ []) (sym (low-comm ((X ↑)) ((X ↑)))) ▸ done

-- xs3 0100: 0 steps
lem-xs3-0100 : ⟪ (X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X3 ∷ []) ⟫ʷ
lem-xs3-0100 = refl

-- xt3 1100: 2 steps
lem-xt3-1100 : ⟪ (X3 ∷ X0 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X3 ∷ []) ⟫ʷ
lem-xt3-1100 = run b0
  where
  b0 : Chain (X3 ∷ X0 ∷ X1 ∷ []) (X0 ∷ X1 ∷ X3 ∷ [])
  b0 = at 0 2 (X0 ∷ X3 ∷ []) (sym (low₁-comm (X) ((X ↑ ↑)))) ▸
       at 1 2 (X1 ∷ X3 ∷ []) (sym (low-comm ((X ↑)) ((X ↑)))) ▸ done

-- xs3 1100: 0 steps
lem-xs3-1100 : ⟪ (X0 ∷ X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X3 ∷ []) ⟫ʷ
lem-xs3-1100 = refl

-- xt3 0010: 1 steps
lem-xt3-0010 : ⟪ (X3 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ []) ⟫ʷ
lem-xt3-0010 = run b0
  where
  b0 : Chain (X3 ∷ X2 ∷ []) (X2 ∷ X3 ∷ [])
  b0 = at 0 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸ done

-- xs3 0010: 0 steps
lem-xs3-0010 : ⟪ (X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ []) ⟫ʷ
lem-xs3-0010 = refl

-- xt3 1010: 2 steps
lem-xt3-1010 : ⟪ (X3 ∷ X0 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xt3-1010 = run b0
  where
  b0 : Chain (X3 ∷ X0 ∷ X2 ∷ []) (X0 ∷ X2 ∷ X3 ∷ [])
  b0 = at 0 2 (X0 ∷ X3 ∷ []) (sym (low₁-comm (X) ((X ↑ ↑)))) ▸
       at 1 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸ done

-- xs3 1010: 0 steps
lem-xs3-1010 : ⟪ (X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xs3-1010 = refl

-- xt3 0110: 2 steps
lem-xt3-0110 : ⟪ (X3 ∷ X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xt3-0110 = run b0
  where
  b0 : Chain (X3 ∷ X1 ∷ X2 ∷ []) (X1 ∷ X2 ∷ X3 ∷ [])
  b0 = at 0 2 (X1 ∷ X3 ∷ []) (sym (low-comm ((X ↑)) ((X ↑)))) ▸
       at 1 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸ done

-- xs3 0110: 0 steps
lem-xs3-0110 : ⟪ (X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xs3-0110 = refl

-- xt3 1110: 3 steps
lem-xt3-1110 : ⟪ (X3 ∷ X0 ∷ X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xt3-1110 = run b0
  where
  b0 : Chain (X3 ∷ X0 ∷ X1 ∷ X2 ∷ []) (X0 ∷ X1 ∷ X2 ∷ X3 ∷ [])
  b0 = at 0 2 (X0 ∷ X3 ∷ []) (sym (low₁-comm (X) ((X ↑ ↑)))) ▸
       at 1 2 (X1 ∷ X3 ∷ []) (sym (low-comm ((X ↑)) ((X ↑)))) ▸
       at 2 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸ done

-- xs3 1110: 0 steps
lem-xs3-1110 : ⟪ (X0 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xs3-1110 = refl

-- xt3 0001: 1 steps
lem-xt3-0001 : ⟪ (X3 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-xt3-0001 = run b0
  where
  b0 : Chain (X3 ∷ X3 ∷ []) []
  b0 = at 0 2 [] wn00390 ▸ done

-- xs3 0001: 1 steps
lem-xs3-0001 : ⟪ (X3 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-xs3-0001 = run b0
  where
  b0 : Chain (X3 ∷ X3 ∷ []) []
  b0 = at 0 2 [] wn00390 ▸ done

-- xt3 1001: 2 steps
lem-xt3-1001 : ⟪ (X3 ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ []) ⟫ʷ
lem-xt3-1001 = run b0
  where
  b0 : Chain (X3 ∷ X0 ∷ X3 ∷ []) (X0 ∷ [])
  b0 = at 0 2 (X0 ∷ X3 ∷ []) (sym (low₁-comm (X) ((X ↑ ↑)))) ▸
       at 1 2 [] wn00390 ▸ done

-- xs3 1001: 1 steps
lem-xs3-1001 : ⟪ (X0 ∷ X3 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ []) ⟫ʷ
lem-xs3-1001 = run b0
  where
  b0 : Chain (X0 ∷ X3 ∷ X3 ∷ []) (X0 ∷ [])
  b0 = at 1 2 [] wn00390 ▸ done

-- xt3 0101: 2 steps
lem-xt3-0101 : ⟪ (X3 ∷ X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ []) ⟫ʷ
lem-xt3-0101 = run b0
  where
  b0 : Chain (X3 ∷ X1 ∷ X3 ∷ []) (X1 ∷ [])
  b0 = at 0 2 (X1 ∷ X3 ∷ []) (sym (low-comm ((X ↑)) ((X ↑)))) ▸
       at 1 2 [] wn00390 ▸ done

-- xs3 0101: 1 steps
lem-xs3-0101 : ⟪ (X1 ∷ X3 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ []) ⟫ʷ
lem-xs3-0101 = run b0
  where
  b0 : Chain (X1 ∷ X3 ∷ X3 ∷ []) (X1 ∷ [])
  b0 = at 1 2 [] wn00390 ▸ done

-- xt3 1101: 3 steps
lem-xt3-1101 : ⟪ (X3 ∷ X0 ∷ X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ []) ⟫ʷ
lem-xt3-1101 = run b0
  where
  b0 : Chain (X3 ∷ X0 ∷ X1 ∷ X3 ∷ []) (X0 ∷ X1 ∷ [])
  b0 = at 0 2 (X0 ∷ X3 ∷ []) (sym (low₁-comm (X) ((X ↑ ↑)))) ▸
       at 1 2 (X1 ∷ X3 ∷ []) (sym (low-comm ((X ↑)) ((X ↑)))) ▸
       at 2 2 [] wn00390 ▸ done

-- xs3 1101: 1 steps
lem-xs3-1101 : ⟪ (X0 ∷ X1 ∷ X3 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ []) ⟫ʷ
lem-xs3-1101 = run b0
  where
  b0 : Chain (X0 ∷ X1 ∷ X3 ∷ X3 ∷ []) (X0 ∷ X1 ∷ [])
  b0 = at 2 2 [] wn00390 ▸ done

-- xt3 0011: 2 steps
lem-xt3-0011 : ⟪ (X3 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ []) ⟫ʷ
lem-xt3-0011 = run b0
  where
  b0 : Chain (X3 ∷ X2 ∷ X3 ∷ []) (X2 ∷ [])
  b0 = at 0 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸
       at 1 2 [] wn00390 ▸ done

-- xs3 0011: 1 steps
lem-xs3-0011 : ⟪ (X2 ∷ X3 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ []) ⟫ʷ
lem-xs3-0011 = run b0
  where
  b0 : Chain (X2 ∷ X3 ∷ X3 ∷ []) (X2 ∷ [])
  b0 = at 1 2 [] wn00390 ▸ done

-- xt3 1011: 3 steps
lem-xt3-1011 : ⟪ (X3 ∷ X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ []) ⟫ʷ
lem-xt3-1011 = run b0
  where
  b0 : Chain (X3 ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X2 ∷ [])
  b0 = at 0 2 (X0 ∷ X3 ∷ []) (sym (low₁-comm (X) ((X ↑ ↑)))) ▸
       at 1 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸
       at 2 2 [] wn00390 ▸ done

-- xs3 1011: 1 steps
lem-xs3-1011 : ⟪ (X0 ∷ X2 ∷ X3 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ []) ⟫ʷ
lem-xs3-1011 = run b0
  where
  b0 : Chain (X0 ∷ X2 ∷ X3 ∷ X3 ∷ []) (X0 ∷ X2 ∷ [])
  b0 = at 2 2 [] wn00390 ▸ done

-- xt3 0111: 3 steps
lem-xt3-0111 : ⟪ (X3 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ []) ⟫ʷ
lem-xt3-0111 = run b0
  where
  b0 : Chain (X3 ∷ X1 ∷ X2 ∷ X3 ∷ []) (X1 ∷ X2 ∷ [])
  b0 = at 0 2 (X1 ∷ X3 ∷ []) (sym (low-comm ((X ↑)) ((X ↑)))) ▸
       at 1 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸
       at 2 2 [] wn00390 ▸ done

-- xs3 0111: 1 steps
lem-xs3-0111 : ⟪ (X1 ∷ X2 ∷ X3 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ []) ⟫ʷ
lem-xs3-0111 = run b0
  where
  b0 : Chain (X1 ∷ X2 ∷ X3 ∷ X3 ∷ []) (X1 ∷ X2 ∷ [])
  b0 = at 2 2 [] wn00390 ▸ done

-- xt3 1111: 4 steps
lem-xt3-1111 : ⟪ (X3 ∷ X0 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X2 ∷ []) ⟫ʷ
lem-xt3-1111 = run b0
  where
  b0 : Chain (X3 ∷ X0 ∷ X1 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X1 ∷ X2 ∷ [])
  b0 = at 0 2 (X0 ∷ X3 ∷ []) (sym (low₁-comm (X) ((X ↑ ↑)))) ▸
       at 1 2 (X1 ∷ X3 ∷ []) (sym (low-comm ((X ↑)) ((X ↑)))) ▸
       at 2 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸
       at 3 2 [] wn00390 ▸ done

-- xs3 1111: 1 steps
lem-xs3-1111 : ⟪ (X0 ∷ X1 ∷ X2 ∷ X3 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X2 ∷ []) ⟫ʷ
lem-xs3-1111 = run b0
  where
  b0 : Chain (X0 ∷ X1 ∷ X2 ∷ X3 ∷ X3 ∷ []) (X0 ∷ X1 ∷ X2 ∷ [])
  b0 = at 3 2 [] wn00390 ▸ done

-- xr0 0000: 0 steps
lem-xr0-0000 : ⟪ [] ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-xr0-0000 = refl

-- xr0 1000: 0 steps
lem-xr0-1000 : ⟪ (X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ []) ⟫ʷ
lem-xr0-1000 = refl

-- xr0 0100: 0 steps
lem-xr0-0100 : ⟪ (X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ []) ⟫ʷ
lem-xr0-0100 = refl

-- xr0 1100: 1 steps
lem-xr0-1100 : ⟪ (X1 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ []) ⟫ʷ
lem-xr0-1100 = run b0
  where
  b0 : Chain (X1 ∷ X0 ∷ []) (X0 ∷ X1 ∷ [])
  b0 = at 0 2 (X0 ∷ X1 ∷ []) (sym (low₁-comm (X) (X))) ▸ done

-- xr0 0010: 0 steps
lem-xr0-0010 : ⟪ (X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ []) ⟫ʷ
lem-xr0-0010 = refl

-- xr0 1010: 0 steps
lem-xr0-1010 : ⟪ (X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ []) ⟫ʷ
lem-xr0-1010 = refl

-- xr0 0110: 0 steps
lem-xr0-0110 : ⟪ (X0 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ []) ⟫ʷ
lem-xr0-0110 = refl

-- xr0 1110: 1 steps
lem-xr0-1110 : ⟪ (X1 ∷ X0 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X2 ∷ []) ⟫ʷ
lem-xr0-1110 = run b0
  where
  b0 : Chain (X1 ∷ X0 ∷ X2 ∷ []) (X0 ∷ X1 ∷ X2 ∷ [])
  b0 = at 0 2 (X0 ∷ X1 ∷ []) (sym (low₁-comm (X) (X))) ▸ done

-- xr0 0001: 0 steps
lem-xr0-0001 : ⟪ (X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ []) ⟫ʷ
lem-xr0-0001 = refl

-- xr0 1001: 0 steps
lem-xr0-1001 : ⟪ (X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X3 ∷ []) ⟫ʷ
lem-xr0-1001 = refl

-- xr0 0101: 0 steps
lem-xr0-0101 : ⟪ (X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ []) ⟫ʷ
lem-xr0-0101 = refl

-- xr0 1101: 1 steps
lem-xr0-1101 : ⟪ (X1 ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X3 ∷ []) ⟫ʷ
lem-xr0-1101 = run b0
  where
  b0 : Chain (X1 ∷ X0 ∷ X3 ∷ []) (X0 ∷ X1 ∷ X3 ∷ [])
  b0 = at 0 2 (X0 ∷ X1 ∷ []) (sym (low₁-comm (X) (X))) ▸ done

-- xr0 0011: 0 steps
lem-xr0-0011 : ⟪ (X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ []) ⟫ʷ
lem-xr0-0011 = refl

-- xr0 1011: 0 steps
lem-xr0-1011 : ⟪ (X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xr0-1011 = refl

-- xr0 0111: 0 steps
lem-xr0-0111 : ⟪ (X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xr0-0111 = refl

-- xr0 1111: 1 steps
lem-xr0-1111 : ⟪ (X1 ∷ X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xr0-1111 = run b0
  where
  b0 : Chain (X1 ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X1 ∷ X2 ∷ X3 ∷ [])
  b0 = at 0 2 (X0 ∷ X1 ∷ []) (sym (low₁-comm (X) (X))) ▸ done

-- xr1 0000: 0 steps
lem-xr1-0000 : ⟪ [] ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-xr1-0000 = refl

-- xr1 1000: 0 steps
lem-xr1-1000 : ⟪ (X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ []) ⟫ʷ
lem-xr1-1000 = refl

-- xr1 0100: 0 steps
lem-xr1-0100 : ⟪ (X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ []) ⟫ʷ
lem-xr1-0100 = refl

-- xr1 1100: 0 steps
lem-xr1-1100 : ⟪ (X0 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ []) ⟫ʷ
lem-xr1-1100 = refl

-- xr1 0010: 0 steps
lem-xr1-0010 : ⟪ (X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ []) ⟫ʷ
lem-xr1-0010 = refl

-- xr1 1010: 0 steps
lem-xr1-1010 : ⟪ (X0 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ []) ⟫ʷ
lem-xr1-1010 = refl

-- xr1 0110: 1 steps
lem-xr1-0110 : ⟪ (X2 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ []) ⟫ʷ
lem-xr1-0110 = run b0
  where
  b0 : Chain (X2 ∷ X1 ∷ []) (X1 ∷ X2 ∷ [])
  b0 = at 0 2 (X1 ∷ X2 ∷ []) (sym (low-comm ((X ↑)) (X))) ▸ done

-- xr1 1110: 1 steps
lem-xr1-1110 : ⟪ (X0 ∷ X2 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X2 ∷ []) ⟫ʷ
lem-xr1-1110 = run b0
  where
  b0 : Chain (X0 ∷ X2 ∷ X1 ∷ []) (X0 ∷ X1 ∷ X2 ∷ [])
  b0 = at 1 2 (X1 ∷ X2 ∷ []) (sym (low-comm ((X ↑)) (X))) ▸ done

-- xr1 0001: 0 steps
lem-xr1-0001 : ⟪ (X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ []) ⟫ʷ
lem-xr1-0001 = refl

-- xr1 1001: 0 steps
lem-xr1-1001 : ⟪ (X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ []) ⟫ʷ
lem-xr1-1001 = refl

-- xr1 0101: 0 steps
lem-xr1-0101 : ⟪ (X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ []) ⟫ʷ
lem-xr1-0101 = refl

-- xr1 1101: 0 steps
lem-xr1-1101 : ⟪ (X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xr1-1101 = refl

-- xr1 0011: 0 steps
lem-xr1-0011 : ⟪ (X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X3 ∷ []) ⟫ʷ
lem-xr1-0011 = refl

-- xr1 1011: 0 steps
lem-xr1-1011 : ⟪ (X0 ∷ X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X3 ∷ []) ⟫ʷ
lem-xr1-1011 = refl

-- xr1 0111: 1 steps
lem-xr1-0111 : ⟪ (X2 ∷ X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xr1-0111 = run b0
  where
  b0 : Chain (X2 ∷ X1 ∷ X3 ∷ []) (X1 ∷ X2 ∷ X3 ∷ [])
  b0 = at 0 2 (X1 ∷ X2 ∷ []) (sym (low-comm ((X ↑)) (X))) ▸ done

-- xr1 1111: 1 steps
lem-xr1-1111 : ⟪ (X0 ∷ X2 ∷ X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xr1-1111 = run b0
  where
  b0 : Chain (X0 ∷ X2 ∷ X1 ∷ X3 ∷ []) (X0 ∷ X1 ∷ X2 ∷ X3 ∷ [])
  b0 = at 1 2 (X1 ∷ X2 ∷ []) (sym (low-comm ((X ↑)) (X))) ▸ done

-- xr2 0000: 0 steps
lem-xr2-0000 : ⟪ [] ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-xr2-0000 = refl

-- xr2 1000: 0 steps
lem-xr2-1000 : ⟪ (X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ []) ⟫ʷ
lem-xr2-1000 = refl

-- xr2 0100: 0 steps
lem-xr2-0100 : ⟪ (X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ []) ⟫ʷ
lem-xr2-0100 = refl

-- xr2 1100: 0 steps
lem-xr2-1100 : ⟪ (X0 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ []) ⟫ʷ
lem-xr2-1100 = refl

-- xr2 0010: 0 steps
lem-xr2-0010 : ⟪ (X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ []) ⟫ʷ
lem-xr2-0010 = refl

-- xr2 1010: 0 steps
lem-xr2-1010 : ⟪ (X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ []) ⟫ʷ
lem-xr2-1010 = refl

-- xr2 0110: 0 steps
lem-xr2-0110 : ⟪ (X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X3 ∷ []) ⟫ʷ
lem-xr2-0110 = refl

-- xr2 1110: 0 steps
lem-xr2-1110 : ⟪ (X0 ∷ X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X3 ∷ []) ⟫ʷ
lem-xr2-1110 = refl

-- xr2 0001: 0 steps
lem-xr2-0001 : ⟪ (X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ []) ⟫ʷ
lem-xr2-0001 = refl

-- xr2 1001: 0 steps
lem-xr2-1001 : ⟪ (X0 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ []) ⟫ʷ
lem-xr2-1001 = refl

-- xr2 0101: 0 steps
lem-xr2-0101 : ⟪ (X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ []) ⟫ʷ
lem-xr2-0101 = refl

-- xr2 1101: 0 steps
lem-xr2-1101 : ⟪ (X0 ∷ X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X2 ∷ []) ⟫ʷ
lem-xr2-1101 = refl

-- xr2 0011: 1 steps
lem-xr2-0011 : ⟪ (X3 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ []) ⟫ʷ
lem-xr2-0011 = run b0
  where
  b0 : Chain (X3 ∷ X2 ∷ []) (X2 ∷ X3 ∷ [])
  b0 = at 0 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸ done

-- xr2 1011: 1 steps
lem-xr2-1011 : ⟪ (X0 ∷ X3 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xr2-1011 = run b0
  where
  b0 : Chain (X0 ∷ X3 ∷ X2 ∷ []) (X0 ∷ X2 ∷ X3 ∷ [])
  b0 = at 1 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸ done

-- xr2 0111: 1 steps
lem-xr2-0111 : ⟪ (X1 ∷ X3 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xr2-0111 = run b0
  where
  b0 : Chain (X1 ∷ X3 ∷ X2 ∷ []) (X1 ∷ X2 ∷ X3 ∷ [])
  b0 = at 1 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸ done

-- xr2 1111: 1 steps
lem-xr2-1111 : ⟪ (X0 ∷ X1 ∷ X3 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xr2-1111 = run b0
  where
  b0 : Chain (X0 ∷ X1 ∷ X3 ∷ X2 ∷ []) (X0 ∷ X1 ∷ X2 ∷ X3 ∷ [])
  b0 = at 2 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸ done

-- b2g 1001R0: 3 steps
lem-b2g-1001R0 : ⟪ (X0 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ []) ⟫ʷ
lem-b2g-1001R0 = run b0
  where
  b0 : Chain (X0 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X0 ∷ X3 ∷ []) (X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ [])
  b0 = at 0 2 (X3 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑ ↑))) ▸
       at 1 3 (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) wn00391 ▸
       at 9 3 (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) wn00392 ▸ done

-- b2g 0011R2: 3 steps
lem-b2g-0011R2 : ⟪ (X2 ∷ X3 ∷ S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ []) ⟫ʷ
lem-b2g-0011R2 = run b0
  where
  b0 : Chain (X2 ∷ X3 ∷ S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ X2 ∷ X3 ∷ []) (X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ [])
  b0 = at 0 2 (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X)) ▸
       at 1 3 (S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ []) wn00393 ▸
       at 9 3 (S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ []) wn00394 ▸ done

-- pass [X3 CS32 X3] [TOFF203]: 67 steps
lem-pass-X3-CS32-X3-vs-TOFF203 : ⟪ (X3 ∷ CS23 ∷ X3 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ X3 ∷ CS23 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS32-X3-vs-TOFF203 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (run b8))))))))
  where
  b0 : Chain (X3 ∷ CS23 ∷ X3 ∷ Toff203 ∷ []) (X3 ∷ CS23 ∷ X3 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ K2 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ [])
  b0 = at 4 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 3 1 (Sw01 ∷ Toff213 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 4 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 5 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 6 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 7 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸ done

  b1 : Chain (X3 ∷ CS23 ∷ X3 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ K2 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ []) (X3 ∷ CS23 ∷ X3 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ Sw01 ∷ Sw01 ∷ [])
  b1 = at 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 10 2 (ι ∷ Sw01 ∷ []) wn00122 ▸
       at 11 2 [] wn00031 ▸ done

  b2 : Chain (X3 ∷ CS23 ∷ X3 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ Sw01 ∷ Sw01 ∷ []) (X3 ∷ CS23 ∷ X3 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ Sw01 ∷ [])
  b2 = at 10 2 (Sw01 ∷ ι1 ∷ []) wn00127 ▸
       at 9 2 (Sw01 ∷ K2 ∷ []) (sym (low-comm (Swap) (K))) ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 9 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 8 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 9 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸ done

  b3 : Chain (X3 ∷ CS23 ∷ X3 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ Sw01 ∷ []) (X3 ∷ Sw01 ∷ CS23 ∷ X3 ∷ Toff213 ∷ Sw01 ∷ [])
  b3 = at 6 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 5 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸
       at 4 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 3 2 (Sw01 ∷ K2 ∷ []) (sym (low-comm (Swap) (K))) ▸
       at 4 8 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) wn00334 ▸
       at 4 8 (Toff213 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸
       at 1 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸ done

  b4 : Chain (X3 ∷ Sw01 ∷ CS23 ∷ X3 ∷ Toff213 ∷ Sw01 ∷ []) (K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ K2 ∷ ι1 ∷ X3 ∷ CS23 ∷ X3 ∷ Sw01 ∷ [])
  b4 = at 0 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸
       at 1 4 (Toff213 ∷ X3 ∷ CS23 ∷ X3 ∷ []) wn00395 ▸
       at 1 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 1 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 2 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 3 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 4 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸ done

  b5 : Chain (K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ K2 ∷ ι1 ∷ X3 ∷ CS23 ∷ X3 ∷ Sw01 ∷ []) (Sw01 ∷ Sw01 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ Sw01 ∷ X3 ∷ CS23 ∷ X3 ∷ Sw01 ∷ [])
  b5 = at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 7 2 (ι ∷ Sw01 ∷ []) wn00122 ▸
       at 0 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸ done

  b6 : Chain (Sw01 ∷ Sw01 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ Sw01 ∷ X3 ∷ CS23 ∷ X3 ∷ Sw01 ∷ []) (Sw01 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ CS12 ∷ Sw01 ∷ Sw23 ∷ K2 ∷ ι ∷ Sw01 ∷ X3 ∷ CS23 ∷ X3 ∷ Sw01 ∷ [])
  b6 = at 1 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 2 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 3 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 4 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 5 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸ done

  b7 : Chain (Sw01 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ CS12 ∷ Sw01 ∷ Sw23 ∷ K2 ∷ ι ∷ Sw01 ∷ X3 ∷ CS23 ∷ X3 ∷ Sw01 ∷ []) (Toff203 ∷ X3 ∷ Sw01 ∷ CS23 ∷ X3 ∷ Sw01 ∷ [])
  b7 = at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 8 2 (ι1 ∷ Sw01 ∷ []) wn00124 ▸
       at 1 8 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) wn00334 ▸
       at 1 8 (Toff213 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff203 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸ done

  b8 : Chain (Toff203 ∷ X3 ∷ Sw01 ∷ CS23 ∷ X3 ∷ Sw01 ∷ []) (Toff203 ∷ X3 ∷ CS23 ∷ X3 ∷ [])
  b8 = at 2 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 3 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸
       at 4 2 [] wn00031 ▸ done

-- pass [X3 CS32 X3] [CS12]: 1 steps
lem-pass-X3-CS32-X3-vs-CS12 : ⟪ (X3 ∷ CS23 ∷ X3 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ X3 ∷ CS23 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS32-X3-vs-CS12 = run b0
  where
  b0 : Chain (X3 ∷ CS23 ∷ X3 ∷ CS12 ∷ []) (CS12 ∷ X3 ∷ CS23 ∷ X3 ∷ [])
  b0 = at 0 4 (CS12 ∷ X3 ∷ CS23 ∷ X3 ∷ []) wn00396 ▸ done

-- pass [X3 CS32 X3] [CSd12]: 1 steps
lem-pass-X3-CS32-X3-vs-CSd12 : ⟪ (X3 ∷ CS23 ∷ X3 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ X3 ∷ CS23 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS32-X3-vs-CSd12 = run b0
  where
  b0 : Chain (X3 ∷ CS23 ∷ X3 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ X3 ∷ CS23 ∷ X3 ∷ [])
  b0 = at 0 4 (CS12⁻ ∷ X3 ∷ CS23 ∷ X3 ∷ []) wn00397 ▸ done

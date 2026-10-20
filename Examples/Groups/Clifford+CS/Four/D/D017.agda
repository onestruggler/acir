{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D017 where

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
open import Examples.Groups.Clifford+CS.Four.Wins.W01 using (wn00001 ; wn00003 ; wn00005 ; wn00012 ; wn00014 ; wn00017 ; wn00018 ; wn00019 ; wn00020 ; wn00021 ; wn00022 ; wn00023 ; wn00024 ; wn00025 ; wn00026 ; wn00027 ; wn00028 ; wn00029 ; wn00030 ; wn00031 ; wn00043 ; wn00046 ; wn00049 ; wn00050 ; wn00051 ; wn00052 ; wn00056 ; wn00107 ; wn00108 ; wn00113 ; wn00114 ; wn00121 ; wn00122 ; wn00123 ; wn00124 ; wn00125 ; wn00157 ; wn00158)
open import Examples.Groups.Clifford+CS.Four.Wins.W02 using (wn00222 ; wn00272 ; wn00333 ; wn00334 ; wn00335 ; wn00336 ; wn00337 ; wn00338 ; wn00339 ; wn00340 ; wn00341 ; wn00342 ; wn00343 ; wn00344 ; wn00345 ; wn00346 ; wn00347 ; wn00348 ; wn00349 ; wn00350 ; wn00351 ; wn00352 ; wn00353 ; wn00354 ; wn00355 ; wn00356 ; wn00357 ; wn00358 ; wn00359 ; wn00360 ; wn00361 ; wn00362 ; wn00363)

-- sw0 TOFF023: 30 steps
lem-sw0-TOFF023 : ⟪ (Sw01 ∷ Toff023 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Toff123 ∷ []) ⟫ʷ
lem-sw0-TOFF023 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Sw01 ∷ Toff023 ∷ Sw01 ∷ []) (Sw01 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 2 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 3 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 4 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 5 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw01 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ []) (K1 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ Sw01 ∷ [])
  b1 = at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 8 2 (ι ∷ Sw01 ∷ []) wn00122 ▸
       at 9 2 [] wn00031 ▸
       at 0 2 (K1 ∷ Sw01 ∷ []) wn00123 ▸ done

  b2 : Chain (K1 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ Sw01 ∷ []) (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ K0 ∷ ι ∷ Sw01 ∷ [])
  b2 = at 1 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 2 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 3 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 4 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b3 : Chain (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ K0 ∷ ι ∷ Sw01 ∷ []) (Toff123 ∷ [])
  b3 = at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K1 ∷ Sw01 ∷ []) wn00123 ▸
       at 7 2 (ι1 ∷ Sw01 ∷ []) wn00124 ▸
       at 0 8 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) wn00125 ▸
       at 0 8 (Toff123 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 TOFF102: 12 steps
lem-sw0-TOFF102 : ⟪ (Sw01 ∷ Toff102 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ []) ⟫ʷ
lem-sw0-TOFF102 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw01 ∷ Toff102 ∷ Sw01 ∷ []) (K0 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K0 ∷ Sw01 ∷ ι ∷ Sw01 ∷ [])
  b0 = at 1 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 1 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 2 2 (CX10 ∷ Sw01 ∷ []) wn00028 ▸
       at 3 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸
       at 4 2 (CX10 ∷ Sw01 ∷ []) wn00028 ▸
       at 5 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 6 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸ done

  b1 : Chain (K0 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K0 ∷ Sw01 ∷ ι ∷ Sw01 ∷ []) (Toff012 ∷ [])
  b1 = at 7 2 (ι1 ∷ Sw01 ∷ []) wn00124 ▸
       at 0 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) wn00272 ▸
       at 0 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 TOFF103: 50 steps
lem-sw0-TOFF103 : ⟪ (Sw01 ∷ Toff103 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ []) ⟫ʷ
lem-sw0-TOFF103 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (run b6))))))
  where
  b0 : Chain (Sw01 ∷ Toff103 ∷ Sw01 ∷ []) (Sw01 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw01 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw01 ∷ []) (K0 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw01 ∷ [])
  b1 = at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 9 2 [] wn00003 ▸
       at 0 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (K0 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw01 ∷ []) (K0 ∷ CS03 ∷ CX10 ∷ Sw23 ∷ CS02⁻ ∷ Sw01 ∷ Sw23 ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw01 ∷ [])
  b2 = at 1 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 2 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 3 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CX10 ∷ Sw01 ∷ []) wn00028 ▸
       at 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 4 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸ done

  b3 : Chain (K0 ∷ CS03 ∷ CX10 ∷ Sw23 ∷ CS02⁻ ∷ Sw01 ∷ Sw23 ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw01 ∷ []) (K0 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ Sw01 ∷ K1 ∷ ι ∷ Sw01 ∷ [])
  b3 = at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 3 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX10 ∷ Sw01 ∷ []) wn00028 ▸
       at 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (K0 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ Sw01 ∷ K1 ∷ ι ∷ Sw01 ∷ []) (Sw23 ∷ K0 ∷ CS02 ∷ CX10 ∷ Sw23 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ CX10 ∷ CS13 ∷ K0 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ [])
  b4 = at 6 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 7 2 (ι1 ∷ Sw01 ∷ []) wn00124 ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸
       at 3 2 (CX10 ∷ Sw23 ∷ []) (sym (low-comm (CX₁₀) (Swap))) ▸
       at 5 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b5 : Chain (Sw23 ∷ K0 ∷ CS02 ∷ CX10 ∷ Sw23 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ CX10 ∷ CS13 ∷ K0 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ []) (Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ [])
  b5 = at 4 2 [] wn00003 ▸
       at 5 2 (CX10 ∷ Sw23 ∷ []) (sym (low-comm (CX₁₀) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸
       at 7 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 8 2 (ι1 ∷ Sw23 ∷ []) (sym (low-comm ((iI ↑)) (Swap))) ▸
       at 1 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) wn00272 ▸
       at 1 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸ done

  b6 : Chain (Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ []) (Toff013 ∷ [])
  b6 = at 0 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 TOFF123: 30 steps
lem-sw0-TOFF123 : ⟪ (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ []) ⟫ʷ
lem-sw0-TOFF123 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) (K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ K1 ∷ ι1 ∷ Sw01 ∷ [])
  b0 = at 1 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 1 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 2 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 3 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 4 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b1 : Chain (K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ K1 ∷ ι1 ∷ Sw01 ∷ []) (Sw01 ∷ K1 ∷ CS23 ∷ Sw01 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ Sw01 ∷ Sw01 ∷ [])
  b1 = at 6 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 7 2 (ι ∷ Sw01 ∷ []) wn00122 ▸
       at 0 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 1 2 (K1 ∷ Sw01 ∷ []) wn00123 ▸
       at 2 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸ done

  b2 : Chain (Sw01 ∷ K1 ∷ CS23 ∷ Sw01 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ Sw01 ∷ Sw01 ∷ []) (Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ K0 ∷ ι ∷ Sw01 ∷ Sw01 ∷ [])
  b2 = at 3 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 4 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 5 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ K0 ∷ ι ∷ Sw01 ∷ Sw01 ∷ []) (Toff023 ∷ [])
  b3 = at 7 2 (K1 ∷ Sw01 ∷ []) wn00123 ▸
       at 8 2 (ι1 ∷ Sw01 ∷ []) wn00124 ▸
       at 1 8 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) wn00125 ▸
       at 1 8 (Toff123 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff023 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 TOFF201: 12 steps
lem-sw0-TOFF201 : ⟪ (Sw01 ∷ Toff201 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ []) ⟫ʷ
lem-sw0-TOFF201 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw01 ∷ Toff201 ∷ Sw01 ∷ []) (K2 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K2 ∷ Sw01 ∷ ι ∷ Sw01 ∷ [])
  b0 = at 1 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 1 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 2 2 (CX10 ∷ Sw01 ∷ []) wn00028 ▸
       at 3 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸
       at 4 2 (CX10 ∷ Sw01 ∷ []) wn00028 ▸
       at 5 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 6 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸ done

  b1 : Chain (K2 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K2 ∷ Sw01 ∷ ι ∷ Sw01 ∷ []) (Toff201 ∷ [])
  b1 = at 7 2 (ι1 ∷ Sw01 ∷ []) wn00124 ▸
       at 0 8 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) wn00333 ▸
       at 0 8 (Toff201 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 TOFF203: 30 steps
lem-sw0-TOFF203 : ⟪ (Sw01 ∷ Toff203 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ []) ⟫ʷ
lem-sw0-TOFF203 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Sw01 ∷ Toff203 ∷ Sw01 ∷ []) (Sw01 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ K2 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Sw01 ∷ Toff213 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 2 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 3 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 4 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 5 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw01 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ K2 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ []) (K2 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ Sw01 ∷ [])
  b1 = at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 8 2 (ι ∷ Sw01 ∷ []) wn00122 ▸
       at 9 2 [] wn00031 ▸
       at 0 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸ done

  b2 : Chain (K2 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ Sw01 ∷ []) (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ K2 ∷ ι ∷ Sw01 ∷ [])
  b2 = at 1 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 2 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 3 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 4 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b3 : Chain (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ K2 ∷ ι ∷ Sw01 ∷ []) (Toff213 ∷ [])
  b3 = at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 7 2 (ι1 ∷ Sw01 ∷ []) wn00124 ▸
       at 0 8 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) wn00334 ▸
       at 0 8 (Toff213 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 TOFF213: 30 steps
lem-sw0-TOFF213 : ⟪ (Sw01 ∷ Toff213 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ []) ⟫ʷ
lem-sw0-TOFF213 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Sw01 ∷ Toff213 ∷ Sw01 ∷ []) (K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ K2 ∷ ι1 ∷ Sw01 ∷ [])
  b0 = at 1 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 1 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 2 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 3 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 4 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b1 : Chain (K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ K2 ∷ ι1 ∷ Sw01 ∷ []) (Sw01 ∷ K2 ∷ CS23 ∷ Sw01 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ Sw01 ∷ Sw01 ∷ [])
  b1 = at 6 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 7 2 (ι ∷ Sw01 ∷ []) wn00122 ▸
       at 0 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 1 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 2 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸ done

  b2 : Chain (Sw01 ∷ K2 ∷ CS23 ∷ Sw01 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ Sw01 ∷ Sw01 ∷ []) (Sw01 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ K2 ∷ ι ∷ Sw01 ∷ Sw01 ∷ [])
  b2 = at 3 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 4 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 5 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (Sw01 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ K2 ∷ ι ∷ Sw01 ∷ Sw01 ∷ []) (Toff203 ∷ [])
  b3 = at 7 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 8 2 (ι1 ∷ Sw01 ∷ []) wn00124 ▸
       at 1 8 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) wn00334 ▸
       at 1 8 (Toff213 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff203 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 TOFF301: 50 steps
lem-sw0-TOFF301 : ⟪ (Sw01 ∷ Toff301 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ []) ⟫ʷ
lem-sw0-TOFF301 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (run b6))))))
  where
  b0 : Chain (Sw01 ∷ Toff301 ∷ Sw01 ∷ []) (Sw01 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (K3 ∷ Sw23 ∷ []) wn00335 ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw01 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw01 ∷ []) (K3 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw01 ∷ [])
  b1 = at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K3 ∷ Sw23 ∷ []) wn00335 ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 9 2 [] wn00003 ▸
       at 0 2 (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑))) ▸
       at 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (K3 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw01 ∷ []) (K3 ∷ CS03 ∷ CX10 ∷ Sw23 ∷ CS02⁻ ∷ Sw01 ∷ Sw23 ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw01 ∷ [])
  b2 = at 1 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 2 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 3 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CX10 ∷ Sw01 ∷ []) wn00028 ▸
       at 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 4 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸ done

  b3 : Chain (K3 ∷ CS03 ∷ CX10 ∷ Sw23 ∷ CS02⁻ ∷ Sw01 ∷ Sw23 ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw01 ∷ []) (K3 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ Sw01 ∷ K3 ∷ ι ∷ Sw01 ∷ [])
  b3 = at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 3 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX10 ∷ Sw01 ∷ []) wn00028 ▸
       at 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (K3 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ Sw01 ∷ K3 ∷ ι ∷ Sw01 ∷ []) (Sw23 ∷ K2 ∷ CS02 ∷ CX10 ∷ Sw23 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ CX10 ∷ CS13 ∷ K3 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ [])
  b4 = at 6 2 (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑))) ▸
       at 7 2 (ι1 ∷ Sw01 ∷ []) wn00124 ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 2 (K2 ∷ Sw23 ∷ []) wn00336 ▸
       at 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸
       at 3 2 (CX10 ∷ Sw23 ∷ []) (sym (low-comm (CX₁₀) (Swap))) ▸
       at 5 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b5 : Chain (Sw23 ∷ K2 ∷ CS02 ∷ CX10 ∷ Sw23 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ CX10 ∷ CS13 ∷ K3 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ []) (Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ [])
  b5 = at 4 2 [] wn00003 ▸
       at 5 2 (CX10 ∷ Sw23 ∷ []) (sym (low-comm (CX₁₀) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸
       at 7 2 (K2 ∷ Sw23 ∷ []) wn00336 ▸
       at 8 2 (ι1 ∷ Sw23 ∷ []) (sym (low-comm ((iI ↑)) (Swap))) ▸
       at 1 8 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) wn00333 ▸
       at 1 8 (Toff201 ∷ []) (by-assoc Eq.refl) ▸ done

  b6 : Chain (Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ []) (Toff301 ∷ [])
  b6 = at 0 3 (Toff301 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 TOFF302: 30 steps
lem-sw0-TOFF302 : ⟪ (Sw01 ∷ Toff302 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ []) ⟫ʷ
lem-sw0-TOFF302 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Sw01 ∷ Toff302 ∷ Sw01 ∷ []) (Sw01 ∷ K3 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ K3 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Sw01 ∷ Toff312 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑))) ▸
       at 2 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 3 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 4 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 5 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw01 ∷ K3 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ K3 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ []) (K3 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K3 ∷ ι ∷ Sw01 ∷ [])
  b1 = at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑))) ▸
       at 8 2 (ι ∷ Sw01 ∷ []) wn00122 ▸
       at 9 2 [] wn00031 ▸
       at 0 2 (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑))) ▸ done

  b2 : Chain (K3 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K3 ∷ ι ∷ Sw01 ∷ []) (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ K3 ∷ ι ∷ Sw01 ∷ [])
  b2 = at 1 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 2 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 3 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 4 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b3 : Chain (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ K3 ∷ ι ∷ Sw01 ∷ []) (Toff312 ∷ [])
  b3 = at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑))) ▸
       at 7 2 (ι1 ∷ Sw01 ∷ []) wn00124 ▸
       at 0 8 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) wn00337 ▸
       at 0 8 (Toff312 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 TOFF312: 30 steps
lem-sw0-TOFF312 : ⟪ (Sw01 ∷ Toff312 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ []) ⟫ʷ
lem-sw0-TOFF312 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Sw01 ∷ Toff312 ∷ Sw01 ∷ []) (K3 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ K3 ∷ ι1 ∷ Sw01 ∷ [])
  b0 = at 1 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑))) ▸
       at 1 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 2 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 3 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 4 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b1 : Chain (K3 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ K3 ∷ ι1 ∷ Sw01 ∷ []) (Sw01 ∷ K3 ∷ CS23 ∷ Sw01 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K3 ∷ ι ∷ Sw01 ∷ Sw01 ∷ [])
  b1 = at 6 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑))) ▸
       at 7 2 (ι ∷ Sw01 ∷ []) wn00122 ▸
       at 0 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 1 2 (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑))) ▸
       at 2 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸ done

  b2 : Chain (Sw01 ∷ K3 ∷ CS23 ∷ Sw01 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K3 ∷ ι ∷ Sw01 ∷ Sw01 ∷ []) (Sw01 ∷ K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ K3 ∷ ι ∷ Sw01 ∷ Sw01 ∷ [])
  b2 = at 3 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 4 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 5 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (Sw01 ∷ K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ K3 ∷ ι ∷ Sw01 ∷ Sw01 ∷ []) (Toff302 ∷ [])
  b3 = at 7 2 (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑))) ▸
       at 8 2 (ι1 ∷ Sw01 ∷ []) wn00124 ▸
       at 1 8 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) wn00337 ▸
       at 1 8 (Toff312 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff302 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00031 ▸ done

-- sw1 S0: 2 steps
lem-sw1-S0 : ⟪ (Sw12 ∷ S0 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ []) ⟫ʷ
lem-sw1-S0 = run b0
  where
  b0 : Chain (Sw12 ∷ S0 ∷ Sw12 ∷ []) (S0 ∷ [])
  b0 = at 0 2 (S0 ∷ Sw12 ∷ []) (sym (low₁-comm (S) (Swap))) ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 Sd0: 2 steps
lem-sw1-Sd0 : ⟪ (Sw12 ∷ S0⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ []) ⟫ʷ
lem-sw1-Sd0 = run b0
  where
  b0 : Chain (Sw12 ∷ S0⁻ ∷ Sw12 ∷ []) (S0⁻ ∷ [])
  b0 = at 0 2 (S0⁻ ∷ Sw12 ∷ []) (sym (low₁-comm ((S • S • S)) (Swap))) ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 K0: 2 steps
lem-sw1-K0 : ⟪ (Sw12 ∷ K0 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ []) ⟫ʷ
lem-sw1-K0 = run b0
  where
  b0 : Chain (Sw12 ∷ K0 ∷ Sw12 ∷ []) (K0 ∷ [])
  b0 = at 0 2 (K0 ∷ Sw12 ∷ []) (sym (low₁-comm (K) (Swap))) ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 Kd0: 2 steps
lem-sw1-Kd0 : ⟪ (Sw12 ∷ K0⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ []) ⟫ʷ
lem-sw1-Kd0 = run b0
  where
  b0 : Chain (Sw12 ∷ K0⁻ ∷ Sw12 ∷ []) (K0⁻ ∷ [])
  b0 = at 0 2 (K0⁻ ∷ Sw12 ∷ []) (sym (low₁-comm ((K • iI)) (Swap))) ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 X0: 2 steps
lem-sw1-X0 : ⟪ (Sw12 ∷ X0 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ []) ⟫ʷ
lem-sw1-X0 = run b0
  where
  b0 : Chain (Sw12 ∷ X0 ∷ Sw12 ∷ []) (X0 ∷ [])
  b0 = at 0 2 (X0 ∷ Sw12 ∷ []) (sym (low₁-comm (X) (Swap))) ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 Z0: 2 steps
lem-sw1-Z0 : ⟪ (Sw12 ∷ Z0 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Z0 ∷ []) ⟫ʷ
lem-sw1-Z0 = run b0
  where
  b0 : Chain (Sw12 ∷ Z0 ∷ Sw12 ∷ []) (Z0 ∷ [])
  b0 = at 0 2 (Z0 ∷ Sw12 ∷ []) (sym (low₁-comm (Z) (Swap))) ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 S1: 2 steps
lem-sw1-S1 : ⟪ (Sw12 ∷ S1 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (S2 ∷ []) ⟫ʷ
lem-sw1-S1 = run b0
  where
  b0 : Chain (Sw12 ∷ S1 ∷ Sw12 ∷ []) (S2 ∷ [])
  b0 = at 0 2 (S2 ∷ Sw12 ∷ []) wn00338 ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 Sd1: 2 steps
lem-sw1-Sd1 : ⟪ (Sw12 ∷ S1⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (S2⁻ ∷ []) ⟫ʷ
lem-sw1-Sd1 = run b0
  where
  b0 : Chain (Sw12 ∷ S1⁻ ∷ Sw12 ∷ []) (S2⁻ ∷ [])
  b0 = at 0 2 (S2⁻ ∷ Sw12 ∷ []) wn00339 ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 K1: 2 steps
lem-sw1-K1 : ⟪ (Sw12 ∷ K1 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ []) ⟫ʷ
lem-sw1-K1 = run b0
  where
  b0 : Chain (Sw12 ∷ K1 ∷ Sw12 ∷ []) (K2 ∷ [])
  b0 = at 0 2 (K2 ∷ Sw12 ∷ []) wn00340 ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 Kd1: 2 steps
lem-sw1-Kd1 : ⟪ (Sw12 ∷ K1⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (K2⁻ ∷ []) ⟫ʷ
lem-sw1-Kd1 = run b0
  where
  b0 : Chain (Sw12 ∷ K1⁻ ∷ Sw12 ∷ []) (K2⁻ ∷ [])
  b0 = at 0 2 (K2⁻ ∷ Sw12 ∷ []) wn00341 ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 X1: 2 steps
lem-sw1-X1 : ⟪ (Sw12 ∷ X1 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ []) ⟫ʷ
lem-sw1-X1 = run b0
  where
  b0 : Chain (Sw12 ∷ X1 ∷ Sw12 ∷ []) (X2 ∷ [])
  b0 = at 0 2 (X2 ∷ Sw12 ∷ []) wn00222 ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 Z1: 2 steps
lem-sw1-Z1 : ⟪ (Sw12 ∷ Z1 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Z2 ∷ []) ⟫ʷ
lem-sw1-Z1 = run b0
  where
  b0 : Chain (Sw12 ∷ Z1 ∷ Sw12 ∷ []) (Z2 ∷ [])
  b0 = at 0 2 (Z2 ∷ Sw12 ∷ []) wn00342 ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 S2: 2 steps
lem-sw1-S2 : ⟪ (Sw12 ∷ S2 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ []) ⟫ʷ
lem-sw1-S2 = run b0
  where
  b0 : Chain (Sw12 ∷ S2 ∷ Sw12 ∷ []) (S1 ∷ [])
  b0 = at 0 2 (S1 ∷ Sw12 ∷ []) wn00343 ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 Sd2: 2 steps
lem-sw1-Sd2 : ⟪ (Sw12 ∷ S2⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ []) ⟫ʷ
lem-sw1-Sd2 = run b0
  where
  b0 : Chain (Sw12 ∷ S2⁻ ∷ Sw12 ∷ []) (S1⁻ ∷ [])
  b0 = at 0 2 (S1⁻ ∷ Sw12 ∷ []) wn00344 ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 K2: 2 steps
lem-sw1-K2 : ⟪ (Sw12 ∷ K2 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ []) ⟫ʷ
lem-sw1-K2 = run b0
  where
  b0 : Chain (Sw12 ∷ K2 ∷ Sw12 ∷ []) (K1 ∷ [])
  b0 = at 0 2 (K1 ∷ Sw12 ∷ []) wn00345 ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 Kd2: 2 steps
lem-sw1-Kd2 : ⟪ (Sw12 ∷ K2⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (K1⁻ ∷ []) ⟫ʷ
lem-sw1-Kd2 = run b0
  where
  b0 : Chain (Sw12 ∷ K2⁻ ∷ Sw12 ∷ []) (K1⁻ ∷ [])
  b0 = at 0 2 (K1⁻ ∷ Sw12 ∷ []) wn00346 ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 X2: 2 steps
lem-sw1-X2 : ⟪ (Sw12 ∷ X2 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ []) ⟫ʷ
lem-sw1-X2 = run b0
  where
  b0 : Chain (Sw12 ∷ X2 ∷ Sw12 ∷ []) (X1 ∷ [])
  b0 = at 0 2 (X1 ∷ Sw12 ∷ []) wn00347 ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 Z2: 2 steps
lem-sw1-Z2 : ⟪ (Sw12 ∷ Z2 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Z1 ∷ []) ⟫ʷ
lem-sw1-Z2 = run b0
  where
  b0 : Chain (Sw12 ∷ Z2 ∷ Sw12 ∷ []) (Z1 ∷ [])
  b0 = at 0 2 (Z1 ∷ Sw12 ∷ []) wn00348 ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 S3: 2 steps
lem-sw1-S3 : ⟪ (Sw12 ∷ S3 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (S3 ∷ []) ⟫ʷ
lem-sw1-S3 = run b0
  where
  b0 : Chain (Sw12 ∷ S3 ∷ Sw12 ∷ []) (S3 ∷ [])
  b0 = at 0 2 (S3 ∷ Sw12 ∷ []) (low₃-comm ((Swap ↑)) (S)) ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 Sd3: 2 steps
lem-sw1-Sd3 : ⟪ (Sw12 ∷ S3⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (S3⁻ ∷ []) ⟫ʷ
lem-sw1-Sd3 = run b0
  where
  b0 : Chain (Sw12 ∷ S3⁻ ∷ Sw12 ∷ []) (S3⁻ ∷ [])
  b0 = at 0 2 (S3⁻ ∷ Sw12 ∷ []) (low₃-comm ((Swap ↑)) ((S • S • S))) ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 K3: 2 steps
lem-sw1-K3 : ⟪ (Sw12 ∷ K3 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (K3 ∷ []) ⟫ʷ
lem-sw1-K3 = run b0
  where
  b0 : Chain (Sw12 ∷ K3 ∷ Sw12 ∷ []) (K3 ∷ [])
  b0 = at 0 2 (K3 ∷ Sw12 ∷ []) (low₃-comm ((Swap ↑)) (K)) ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 Kd3: 2 steps
lem-sw1-Kd3 : ⟪ (Sw12 ∷ K3⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (K3⁻ ∷ []) ⟫ʷ
lem-sw1-Kd3 = run b0
  where
  b0 : Chain (Sw12 ∷ K3⁻ ∷ Sw12 ∷ []) (K3⁻ ∷ [])
  b0 = at 0 2 (K3⁻ ∷ Sw12 ∷ []) (low₃-comm ((Swap ↑)) ((K • iI))) ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 X3: 2 steps
lem-sw1-X3 : ⟪ (Sw12 ∷ X3 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ []) ⟫ʷ
lem-sw1-X3 = run b0
  where
  b0 : Chain (Sw12 ∷ X3 ∷ Sw12 ∷ []) (X3 ∷ [])
  b0 = at 0 2 (X3 ∷ Sw12 ∷ []) (low₃-comm ((Swap ↑)) (X)) ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 Z3: 2 steps
lem-sw1-Z3 : ⟪ (Sw12 ∷ Z3 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Z3 ∷ []) ⟫ʷ
lem-sw1-Z3 = run b0
  where
  b0 : Chain (Sw12 ∷ Z3 ∷ Sw12 ∷ []) (Z3 ∷ [])
  b0 = at 0 2 (Z3 ∷ Sw12 ∷ []) (low₃-comm ((Swap ↑)) (Z)) ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 CS01: 3 steps
lem-sw1-CS01 : ⟪ (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ []) ⟫ʷ
lem-sw1-CS01 = run b0
  where
  b0 : Chain (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (CS02 ∷ [])
  b0 = at 2 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 0 3 (CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 CSd01: 3 steps
lem-sw1-CSd01 : ⟪ (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ []) ⟫ʷ
lem-sw1-CSd01 = run b0
  where
  b0 : Chain (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) (CS02⁻ ∷ [])
  b0 = at 2 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 0 3 (CS02⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 CZ01: 3 steps
lem-sw1-CZ01 : ⟪ (Sw12 ∷ CZ01 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CZ02 ∷ []) ⟫ʷ
lem-sw1-CZ01 = run b0
  where
  b0 : Chain (Sw12 ∷ CZ01 ∷ Sw12 ∷ []) (CZ02 ∷ [])
  b0 = at 2 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 0 3 (CZ02 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 CX01: 3 steps
lem-sw1-CX01 : ⟪ (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CX02 ∷ []) ⟫ʷ
lem-sw1-CX01 = run b0
  where
  b0 : Chain (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (CX02 ∷ [])
  b0 = at 2 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 0 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 CK01: 3 steps
lem-sw1-CK01 : ⟪ (Sw12 ∷ CK01 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK02 ∷ []) ⟫ʷ
lem-sw1-CK01 = run b0
  where
  b0 : Chain (Sw12 ∷ CK01 ∷ Sw12 ∷ []) (CK02 ∷ [])
  b0 = at 2 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 0 3 (CK02 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 CKd01: 3 steps
lem-sw1-CKd01 : ⟪ (Sw12 ∷ CK01⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK02⁻ ∷ []) ⟫ʷ
lem-sw1-CKd01 = run b0
  where
  b0 : Chain (Sw12 ∷ CK01⁻ ∷ Sw12 ∷ []) (CK02⁻ ∷ [])
  b0 = at 2 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 0 3 (CK02⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 CS02: 3 steps
lem-sw1-CS02 : ⟪ (Sw12 ∷ CS02 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ []) ⟫ʷ
lem-sw1-CS02 = run b0
  where
  b0 : Chain (Sw12 ∷ CS02 ∷ Sw12 ∷ []) (CS01 ∷ [])
  b0 = at 1 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] wn00014 ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 CSd02: 3 steps
lem-sw1-CSd02 : ⟪ (Sw12 ∷ CS02⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ []) ⟫ʷ
lem-sw1-CSd02 = run b0
  where
  b0 : Chain (Sw12 ∷ CS02⁻ ∷ Sw12 ∷ []) (CS01⁻ ∷ [])
  b0 = at 1 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] wn00014 ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 CZ02: 3 steps
lem-sw1-CZ02 : ⟪ (Sw12 ∷ CZ02 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CZ01 ∷ []) ⟫ʷ
lem-sw1-CZ02 = run b0
  where
  b0 : Chain (Sw12 ∷ CZ02 ∷ Sw12 ∷ []) (CZ01 ∷ [])
  b0 = at 1 1 (Sw12 ∷ CZ01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] wn00014 ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 CX02: 3 steps
lem-sw1-CX02 : ⟪ (Sw12 ∷ CX02 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CX01 ∷ []) ⟫ʷ
lem-sw1-CX02 = run b0
  where
  b0 : Chain (Sw12 ∷ CX02 ∷ Sw12 ∷ []) (CX01 ∷ [])
  b0 = at 1 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] wn00014 ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 CK02: 3 steps
lem-sw1-CK02 : ⟪ (Sw12 ∷ CK02 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK01 ∷ []) ⟫ʷ
lem-sw1-CK02 = run b0
  where
  b0 : Chain (Sw12 ∷ CK02 ∷ Sw12 ∷ []) (CK01 ∷ [])
  b0 = at 1 1 (Sw12 ∷ CK01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] wn00014 ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 CKd02: 3 steps
lem-sw1-CKd02 : ⟪ (Sw12 ∷ CK02⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK01⁻ ∷ []) ⟫ʷ
lem-sw1-CKd02 = run b0
  where
  b0 : Chain (Sw12 ∷ CK02⁻ ∷ Sw12 ∷ []) (CK01⁻ ∷ [])
  b0 = at 1 1 (Sw12 ∷ CK01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] wn00014 ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 CS03: 6 steps
lem-sw1-CS03 : ⟪ (Sw12 ∷ CS03 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ []) ⟫ʷ
lem-sw1-CS03 = run b0
  where
  b0 : Chain (Sw12 ∷ CS03 ∷ Sw12 ∷ []) (CS03 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) wn00022 ▸
       at 2 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 3 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) wn00023 ▸
       at 0 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 CSd03: 6 steps
lem-sw1-CSd03 : ⟪ (Sw12 ∷ CS03⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ []) ⟫ʷ
lem-sw1-CSd03 = run b0
  where
  b0 : Chain (Sw12 ∷ CS03⁻ ∷ Sw12 ∷ []) (CS03⁻ ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) wn00022 ▸
       at 2 2 (CS01⁻ ∷ Sw23 ∷ []) (sym (low-comm ((CS • CS • CS)) (Swap))) ▸
       at 3 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) wn00023 ▸
       at 0 5 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 CZ03: 6 steps
lem-sw1-CZ03 : ⟪ (Sw12 ∷ CZ03 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CZ03 ∷ []) ⟫ʷ
lem-sw1-CZ03 = run b0
  where
  b0 : Chain (Sw12 ∷ CZ03 ∷ Sw12 ∷ []) (CZ03 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) wn00022 ▸
       at 2 2 (CZ01 ∷ Sw23 ∷ []) (sym (low-comm (CZ) (Swap))) ▸
       at 3 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) wn00023 ▸
       at 0 5 (CZ03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 CX03: 6 steps
lem-sw1-CX03 : ⟪ (Sw12 ∷ CX03 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CX03 ∷ []) ⟫ʷ
lem-sw1-CX03 = run b0
  where
  b0 : Chain (Sw12 ∷ CX03 ∷ Sw12 ∷ []) (CX03 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) wn00022 ▸
       at 2 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 3 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) wn00023 ▸
       at 0 5 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 CK03: 6 steps
lem-sw1-CK03 : ⟪ (Sw12 ∷ CK03 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK03 ∷ []) ⟫ʷ
lem-sw1-CK03 = run b0
  where
  b0 : Chain (Sw12 ∷ CK03 ∷ Sw12 ∷ []) (CK03 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) wn00022 ▸
       at 2 2 (CK01 ∷ Sw23 ∷ []) (sym (low-comm (CK₀₁) (Swap))) ▸
       at 3 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) wn00023 ▸
       at 0 5 (CK03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 CKd03: 6 steps
lem-sw1-CKd03 : ⟪ (Sw12 ∷ CK03⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK03⁻ ∷ []) ⟫ʷ
lem-sw1-CKd03 = run b0
  where
  b0 : Chain (Sw12 ∷ CK03⁻ ∷ Sw12 ∷ []) (CK03⁻ ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw12 ∷ CK01⁻ ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) wn00022 ▸
       at 2 2 (CK01⁻ ∷ Sw23 ∷ []) (sym (low-comm ((S • CK₀₁)) (Swap))) ▸
       at 3 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) wn00023 ▸
       at 0 5 (CK03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 CX10: 3 steps
lem-sw1-CX10 : ⟪ (Sw12 ∷ CX10 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CX20 ∷ []) ⟫ʷ
lem-sw1-CX10 = run b0
  where
  b0 : Chain (Sw12 ∷ CX10 ∷ Sw12 ∷ []) (CX20 ∷ [])
  b0 = at 2 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 0 3 (CX20 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 CK10: 3 steps
lem-sw1-CK10 : ⟪ (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK20 ∷ []) ⟫ʷ
lem-sw1-CK10 = run b0
  where
  b0 : Chain (Sw12 ∷ CK10 ∷ Sw12 ∷ []) (CK20 ∷ [])
  b0 = at 2 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 0 3 (CK20 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 CKd10: 3 steps
lem-sw1-CKd10 : ⟪ (Sw12 ∷ CK10⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK20⁻ ∷ []) ⟫ʷ
lem-sw1-CKd10 = run b0
  where
  b0 : Chain (Sw12 ∷ CK10⁻ ∷ Sw12 ∷ []) (CK20⁻ ∷ [])
  b0 = at 2 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 0 3 (CK20⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 CS12: 2 steps
lem-sw1-CS12 : ⟪ (Sw12 ∷ CS12 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ []) ⟫ʷ
lem-sw1-CS12 = run b0
  where
  b0 : Chain (Sw12 ∷ CS12 ∷ Sw12 ∷ []) (CS12 ∷ [])
  b0 = at 0 2 (CS12 ∷ Sw12 ∷ []) wn00018 ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 CSd12: 2 steps
lem-sw1-CSd12 : ⟪ (Sw12 ∷ CS12⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ []) ⟫ʷ
lem-sw1-CSd12 = run b0
  where
  b0 : Chain (Sw12 ∷ CS12⁻ ∷ Sw12 ∷ []) (CS12⁻ ∷ [])
  b0 = at 0 2 (CS12⁻ ∷ Sw12 ∷ []) wn00019 ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 CZ12: 2 steps
lem-sw1-CZ12 : ⟪ (Sw12 ∷ CZ12 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CZ12 ∷ []) ⟫ʷ
lem-sw1-CZ12 = run b0
  where
  b0 : Chain (Sw12 ∷ CZ12 ∷ Sw12 ∷ []) (CZ12 ∷ [])
  b0 = at 0 2 (CZ12 ∷ Sw12 ∷ []) wn00349 ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 CX12: 2 steps
lem-sw1-CX12 : ⟪ (Sw12 ∷ CX12 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CX21 ∷ []) ⟫ʷ
lem-sw1-CX12 = run b0
  where
  b0 : Chain (Sw12 ∷ CX12 ∷ Sw12 ∷ []) (CX21 ∷ [])
  b0 = at 0 2 (CX21 ∷ Sw12 ∷ []) wn00050 ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 CK12: 2 steps
lem-sw1-CK12 : ⟪ (Sw12 ∷ CK12 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK21 ∷ []) ⟫ʷ
lem-sw1-CK12 = run b0
  where
  b0 : Chain (Sw12 ∷ CK12 ∷ Sw12 ∷ []) (CK21 ∷ [])
  b0 = at 0 2 (CK21 ∷ Sw12 ∷ []) wn00350 ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 CKd12: 2 steps
lem-sw1-CKd12 : ⟪ (Sw12 ∷ CK12⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK21⁻ ∷ []) ⟫ʷ
lem-sw1-CKd12 = run b0
  where
  b0 : Chain (Sw12 ∷ CK12⁻ ∷ Sw12 ∷ []) (CK21⁻ ∷ [])
  b0 = at 0 2 (CK21⁻ ∷ Sw12 ∷ []) wn00351 ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 CS13: 2 steps
lem-sw1-CS13 : ⟪ (Sw12 ∷ CS13 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ []) ⟫ʷ
lem-sw1-CS13 = run b0
  where
  b0 : Chain (Sw12 ∷ CS13 ∷ Sw12 ∷ []) (CS23 ∷ [])
  b0 = at 0 2 (CS23 ∷ Sw12 ∷ []) wn00020 ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 CSd13: 2 steps
lem-sw1-CSd13 : ⟪ (Sw12 ∷ CS13⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ []) ⟫ʷ
lem-sw1-CSd13 = run b0
  where
  b0 : Chain (Sw12 ∷ CS13⁻ ∷ Sw12 ∷ []) (CS23⁻ ∷ [])
  b0 = at 0 2 (CS23⁻ ∷ Sw12 ∷ []) wn00021 ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 CZ13: 2 steps
lem-sw1-CZ13 : ⟪ (Sw12 ∷ CZ13 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CZ23 ∷ []) ⟫ʷ
lem-sw1-CZ13 = run b0
  where
  b0 : Chain (Sw12 ∷ CZ13 ∷ Sw12 ∷ []) (CZ23 ∷ [])
  b0 = at 0 2 (CZ23 ∷ Sw12 ∷ []) wn00107 ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 CX13: 2 steps
lem-sw1-CX13 : ⟪ (Sw12 ∷ CX13 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ []) ⟫ʷ
lem-sw1-CX13 = run b0
  where
  b0 : Chain (Sw12 ∷ CX13 ∷ Sw12 ∷ []) (CX23 ∷ [])
  b0 = at 0 2 (CX23 ∷ Sw12 ∷ []) wn00157 ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 CK13: 2 steps
lem-sw1-CK13 : ⟪ (Sw12 ∷ CK13 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK23 ∷ []) ⟫ʷ
lem-sw1-CK13 = run b0
  where
  b0 : Chain (Sw12 ∷ CK13 ∷ Sw12 ∷ []) (CK23 ∷ [])
  b0 = at 0 2 (CK23 ∷ Sw12 ∷ []) wn00352 ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 CKd13: 2 steps
lem-sw1-CKd13 : ⟪ (Sw12 ∷ CK13⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK23⁻ ∷ []) ⟫ʷ
lem-sw1-CKd13 = run b0
  where
  b0 : Chain (Sw12 ∷ CK13⁻ ∷ Sw12 ∷ []) (CK23⁻ ∷ [])
  b0 = at 0 2 (CK23⁻ ∷ Sw12 ∷ []) wn00353 ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 CX20: 3 steps
lem-sw1-CX20 : ⟪ (Sw12 ∷ CX20 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CX10 ∷ []) ⟫ʷ
lem-sw1-CX20 = run b0
  where
  b0 : Chain (Sw12 ∷ CX20 ∷ Sw12 ∷ []) (CX10 ∷ [])
  b0 = at 1 1 (Sw12 ∷ CX10 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] wn00014 ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 CK20: 3 steps
lem-sw1-CK20 : ⟪ (Sw12 ∷ CK20 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK10 ∷ []) ⟫ʷ
lem-sw1-CK20 = run b0
  where
  b0 : Chain (Sw12 ∷ CK20 ∷ Sw12 ∷ []) (CK10 ∷ [])
  b0 = at 1 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] wn00014 ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 CKd20: 3 steps
lem-sw1-CKd20 : ⟪ (Sw12 ∷ CK20⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK10⁻ ∷ []) ⟫ʷ
lem-sw1-CKd20 = run b0
  where
  b0 : Chain (Sw12 ∷ CK20⁻ ∷ Sw12 ∷ []) (CK10⁻ ∷ [])
  b0 = at 1 1 (Sw12 ∷ CK10⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] wn00014 ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 CX21: 2 steps
lem-sw1-CX21 : ⟪ (Sw12 ∷ CX21 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CX12 ∷ []) ⟫ʷ
lem-sw1-CX21 = run b0
  where
  b0 : Chain (Sw12 ∷ CX21 ∷ Sw12 ∷ []) (CX12 ∷ [])
  b0 = at 0 2 (CX12 ∷ Sw12 ∷ []) wn00354 ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 CK21: 2 steps
lem-sw1-CK21 : ⟪ (Sw12 ∷ CK21 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK12 ∷ []) ⟫ʷ
lem-sw1-CK21 = run b0
  where
  b0 : Chain (Sw12 ∷ CK21 ∷ Sw12 ∷ []) (CK12 ∷ [])
  b0 = at 0 2 (CK12 ∷ Sw12 ∷ []) wn00355 ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 CKd21: 2 steps
lem-sw1-CKd21 : ⟪ (Sw12 ∷ CK21⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK12⁻ ∷ []) ⟫ʷ
lem-sw1-CKd21 = run b0
  where
  b0 : Chain (Sw12 ∷ CK21⁻ ∷ Sw12 ∷ []) (CK12⁻ ∷ [])
  b0 = at 0 2 (CK12⁻ ∷ Sw12 ∷ []) wn00356 ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 CS23: 2 steps
lem-sw1-CS23 : ⟪ (Sw12 ∷ CS23 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ []) ⟫ʷ
lem-sw1-CS23 = run b0
  where
  b0 : Chain (Sw12 ∷ CS23 ∷ Sw12 ∷ []) (CS13 ∷ [])
  b0 = at 0 2 (CS13 ∷ Sw12 ∷ []) wn00049 ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 CSd23: 2 steps
lem-sw1-CSd23 : ⟪ (Sw12 ∷ CS23⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ []) ⟫ʷ
lem-sw1-CSd23 = run b0
  where
  b0 : Chain (Sw12 ∷ CS23⁻ ∷ Sw12 ∷ []) (CS13⁻ ∷ [])
  b0 = at 0 2 (CS13⁻ ∷ Sw12 ∷ []) wn00051 ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 CZ23: 2 steps
lem-sw1-CZ23 : ⟪ (Sw12 ∷ CZ23 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CZ13 ∷ []) ⟫ʷ
lem-sw1-CZ23 = run b0
  where
  b0 : Chain (Sw12 ∷ CZ23 ∷ Sw12 ∷ []) (CZ13 ∷ [])
  b0 = at 0 2 (CZ13 ∷ Sw12 ∷ []) wn00108 ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 CX23: 2 steps
lem-sw1-CX23 : ⟪ (Sw12 ∷ CX23 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CX13 ∷ []) ⟫ʷ
lem-sw1-CX23 = run b0
  where
  b0 : Chain (Sw12 ∷ CX23 ∷ Sw12 ∷ []) (CX13 ∷ [])
  b0 = at 0 2 (CX13 ∷ Sw12 ∷ []) wn00158 ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 CK23: 2 steps
lem-sw1-CK23 : ⟪ (Sw12 ∷ CK23 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK13 ∷ []) ⟫ʷ
lem-sw1-CK23 = run b0
  where
  b0 : Chain (Sw12 ∷ CK23 ∷ Sw12 ∷ []) (CK13 ∷ [])
  b0 = at 0 2 (CK13 ∷ Sw12 ∷ []) wn00357 ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 CKd23: 2 steps
lem-sw1-CKd23 : ⟪ (Sw12 ∷ CK23⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK13⁻ ∷ []) ⟫ʷ
lem-sw1-CKd23 = run b0
  where
  b0 : Chain (Sw12 ∷ CK23⁻ ∷ Sw12 ∷ []) (CK13⁻ ∷ [])
  b0 = at 0 2 (CK13⁻ ∷ Sw12 ∷ []) wn00358 ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 CX30: 6 steps
lem-sw1-CX30 : ⟪ (Sw12 ∷ CX30 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CX30 ∷ []) ⟫ʷ
lem-sw1-CX30 = run b0
  where
  b0 : Chain (Sw12 ∷ CX30 ∷ Sw12 ∷ []) (CX30 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) wn00022 ▸
       at 2 2 (CX10 ∷ Sw23 ∷ []) (sym (low-comm (CX₁₀) (Swap))) ▸
       at 3 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) wn00023 ▸
       at 0 5 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 CK30: 6 steps
lem-sw1-CK30 : ⟪ (Sw12 ∷ CK30 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK30 ∷ []) ⟫ʷ
lem-sw1-CK30 = run b0
  where
  b0 : Chain (Sw12 ∷ CK30 ∷ Sw12 ∷ []) (CK30 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) wn00022 ▸
       at 2 2 (CK10 ∷ Sw23 ∷ []) (sym (low-comm (CK₁₀) (Swap))) ▸
       at 3 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) wn00023 ▸
       at 0 5 (CK30 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 CKd30: 6 steps
lem-sw1-CKd30 : ⟪ (Sw12 ∷ CK30⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK30⁻ ∷ []) ⟫ʷ
lem-sw1-CKd30 = run b0
  where
  b0 : Chain (Sw12 ∷ CK30⁻ ∷ Sw12 ∷ []) (CK30⁻ ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) wn00022 ▸
       at 2 2 (CK10⁻ ∷ Sw23 ∷ []) (sym (low-comm ((S ↑ • CK₁₀)) (Swap))) ▸
       at 3 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) wn00023 ▸
       at 0 5 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 CX31: 2 steps
lem-sw1-CX31 : ⟪ (Sw12 ∷ CX31 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CX32 ∷ []) ⟫ʷ
lem-sw1-CX31 = run b0
  where
  b0 : Chain (Sw12 ∷ CX31 ∷ Sw12 ∷ []) (CX32 ∷ [])
  b0 = at 0 2 (CX32 ∷ Sw12 ∷ []) wn00113 ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 CK31: 2 steps
lem-sw1-CK31 : ⟪ (Sw12 ∷ CK31 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK32 ∷ []) ⟫ʷ
lem-sw1-CK31 = run b0
  where
  b0 : Chain (Sw12 ∷ CK31 ∷ Sw12 ∷ []) (CK32 ∷ [])
  b0 = at 0 2 (CK32 ∷ Sw12 ∷ []) wn00359 ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 CKd31: 2 steps
lem-sw1-CKd31 : ⟪ (Sw12 ∷ CK31⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK32⁻ ∷ []) ⟫ʷ
lem-sw1-CKd31 = run b0
  where
  b0 : Chain (Sw12 ∷ CK31⁻ ∷ Sw12 ∷ []) (CK32⁻ ∷ [])
  b0 = at 0 2 (CK32⁻ ∷ Sw12 ∷ []) wn00360 ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 CX32: 2 steps
lem-sw1-CX32 : ⟪ (Sw12 ∷ CX32 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CX31 ∷ []) ⟫ʷ
lem-sw1-CX32 = run b0
  where
  b0 : Chain (Sw12 ∷ CX32 ∷ Sw12 ∷ []) (CX31 ∷ [])
  b0 = at 0 2 (CX31 ∷ Sw12 ∷ []) wn00114 ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 CK32: 2 steps
lem-sw1-CK32 : ⟪ (Sw12 ∷ CK32 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK31 ∷ []) ⟫ʷ
lem-sw1-CK32 = run b0
  where
  b0 : Chain (Sw12 ∷ CK32 ∷ Sw12 ∷ []) (CK31 ∷ [])
  b0 = at 0 2 (CK31 ∷ Sw12 ∷ []) wn00361 ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 CKd32: 2 steps
lem-sw1-CKd32 : ⟪ (Sw12 ∷ CK32⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK31⁻ ∷ []) ⟫ʷ
lem-sw1-CKd32 = run b0
  where
  b0 : Chain (Sw12 ∷ CK32⁻ ∷ Sw12 ∷ []) (CK31⁻ ∷ [])
  b0 = at 0 2 (CK31⁻ ∷ Sw12 ∷ []) wn00362 ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 CCZ012: 12 steps
lem-sw1-CCZ012 : ⟪ (Sw12 ∷ CCZ012 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ []) ⟫ʷ
lem-sw1-CCZ012 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw12 ∷ CCZ012 ∷ Sw12 ∷ []) (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ Sw12 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (CS12 ∷ Sw12 ∷ []) wn00018 ▸
       at 3 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 1 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CS12⁻ ∷ Sw12 ∷ []) wn00019 ▸
       at 5 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 3 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ Sw12 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw12 ∷ []) (CCZ012 ∷ [])
  b1 = at 4 2 [] wn00014 ▸
       at 0 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00017 ▸
       at 0 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 CCZ013: 36 steps
lem-sw1-CCZ013 : ⟪ (Sw12 ∷ CCZ013 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ []) ⟫ʷ
lem-sw1-CCZ013 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (run b4))))
  where
  b0 : Chain (Sw12 ∷ CCZ013 ∷ Sw12 ∷ []) (Sw12 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b1 : Chain (Sw12 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw12 ∷ []) (CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS03 ∷ Sw12 ∷ [])
  b1 = at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸
       at 0 2 (CS23 ∷ Sw12 ∷ []) wn00020 ▸
       at 3 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 1 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CS23⁻ ∷ Sw12 ∷ []) wn00021 ▸
       at 5 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸ done

  b2 : Chain (CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS03 ∷ Sw12 ∷ []) (Sw01 ∷ CS23 ∷ Sw01 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw12 ∷ Sw12 ∷ [])
  b2 = at 3 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) wn00022 ▸
       at 6 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 7 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) wn00023 ▸
       at 4 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 1 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸ done

  b3 : Chain (Sw01 ∷ CS23 ∷ Sw01 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw12 ∷ Sw12 ∷ []) (Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw12 ∷ Sw12 ∷ [])
  b3 = at 2 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 3 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 4 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw12 ∷ Sw12 ∷ []) (CCZ023 ∷ [])
  b4 = at 1 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸
       at 1 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 CCZ023: 36 steps
lem-sw1-CCZ023 : ⟪ (Sw12 ∷ CCZ023 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ []) ⟫ʷ
lem-sw1-CCZ023 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (run b4))))
  where
  b0 : Chain (Sw12 ∷ CCZ023 ∷ Sw12 ∷ []) (Sw12 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 2 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 3 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 4 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b1 : Chain (Sw12 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ []) (CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw12 ∷ CX02 ∷ CS03 ∷ Sw12 ∷ [])
  b1 = at 6 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00031 ▸
       at 0 2 (CS13 ∷ Sw12 ∷ []) wn00049 ▸
       at 2 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00014 ▸
       at 2 2 (CS13⁻ ∷ Sw12 ∷ []) wn00051 ▸ done

  b2 : Chain (CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw12 ∷ CX02 ∷ CS03 ∷ Sw12 ∷ []) (Sw23 ∷ Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw12 ∷ Sw12 ∷ [])
  b2 = at 4 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00014 ▸
       at 5 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) wn00022 ▸
       at 6 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 7 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) wn00023 ▸
       at 4 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b3 : Chain (Sw23 ∷ Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw12 ∷ Sw12 ∷ []) (Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ [])
  b3 = at 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00003 ▸
       at 2 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸ done

  b4 : Chain (Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ []) (CCZ013 ∷ [])
  b4 = at 1 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00043 ▸
       at 1 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 CCZ123: 9 steps
lem-sw1-CCZ123 : ⟪ (Sw12 ∷ CCZ123 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ []) ⟫ʷ
lem-sw1-CCZ123 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw12 ∷ CCZ123 ∷ Sw12 ∷ []) (CCZ123 ∷ Sw12 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (CS13 ∷ Sw12 ∷ []) wn00049 ▸
       at 1 2 (CX21 ∷ Sw12 ∷ []) wn00050 ▸
       at 2 2 (CS13⁻ ∷ Sw12 ∷ []) wn00051 ▸
       at 3 2 (CX21 ∷ Sw12 ∷ []) wn00050 ▸
       at 4 2 (CS23 ∷ Sw12 ∷ []) wn00020 ▸
       at 0 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00052 ▸
       at 0 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (CCZ123 ∷ Sw12 ∷ Sw12 ∷ []) (CCZ123 ∷ [])
  b1 = at 1 2 [] wn00014 ▸ done

-- sw1 TOFF012: 15 steps
lem-sw1-TOFF012 : ⟪ (Sw12 ∷ Toff012 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ []) ⟫ʷ
lem-sw1-TOFF012 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw12 ∷ Toff012 ∷ Sw12 ∷ []) (K0 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ Sw12 ∷ CS02 ∷ K0 ∷ ι ∷ Sw12 ∷ [])
  b0 = at 1 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (K0 ∷ Sw12 ∷ []) (sym (low₁-comm (K) (Swap))) ▸
       at 1 2 (CS12 ∷ Sw12 ∷ []) wn00018 ▸
       at 4 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 2 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS12⁻ ∷ Sw12 ∷ []) wn00019 ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (K0 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ Sw12 ∷ CS02 ∷ K0 ∷ ι ∷ Sw12 ∷ []) (Toff012 ∷ [])
  b1 = at 6 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00014 ▸
       at 6 2 (K0 ∷ Sw12 ∷ []) (sym (low₁-comm (K) (Swap))) ▸
       at 7 2 (ι ∷ Sw12 ∷ []) (sym (low₁-comm (iI) (Swap))) ▸
       at 0 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) wn00046 ▸
       at 0 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 TOFF013: 45 steps
lem-sw1-TOFF013 : ⟪ (Sw12 ∷ Toff013 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ []) ⟫ʷ
lem-sw1-TOFF013 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (run b5)))))
  where
  b0 : Chain (Sw12 ∷ Toff013 ∷ Sw12 ∷ []) (Sw12 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw12 ∷ []) (K0 ∷ CS23 ∷ Sw12 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw12 ∷ [])
  b1 = at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 9 2 [] wn00003 ▸
       at 0 2 (K0 ∷ Sw12 ∷ []) (sym (low₁-comm (K) (Swap))) ▸
       at 1 2 (CS23 ∷ Sw12 ∷ []) wn00020 ▸ done

  b2 : Chain (K0 ∷ CS23 ∷ Sw12 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw12 ∷ []) (K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw12 ∷ [])
  b2 = at 4 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 2 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS23⁻ ∷ Sw12 ∷ []) wn00021 ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) wn00022 ▸
       at 7 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸ done

  b3 : Chain (K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw12 ∷ []) (Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ Sw01 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw12 ∷ [])
  b3 = at 8 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) wn00023 ▸
       at 5 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K0 ∷ Sw12 ∷ []) (sym (low₁-comm (K) (Swap))) ▸
       at 7 2 (ι ∷ Sw12 ∷ []) (sym (low₁-comm (iI) (Swap))) ▸
       at 0 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 1 2 (K1 ∷ Sw01 ∷ []) wn00123 ▸
       at 2 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 3 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸ done

  b4 : Chain (Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ Sw01 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw12 ∷ []) (Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ Sw01 ∷ ι ∷ Sw12 ∷ Sw12 ∷ [])
  b4 = at 4 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 5 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K1 ∷ Sw01 ∷ []) wn00123 ▸ done

  b5 : Chain (Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ Sw01 ∷ ι ∷ Sw12 ∷ Sw12 ∷ []) (Toff023 ∷ [])
  b5 = at 8 2 (ι1 ∷ Sw01 ∷ []) wn00124 ▸
       at 1 8 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) wn00125 ▸
       at 1 8 (Toff123 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff023 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 TOFF023: 45 steps
lem-sw1-TOFF023 : ⟪ (Sw12 ∷ Toff023 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ []) ⟫ʷ
lem-sw1-TOFF023 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (run b5)))))
  where
  b0 : Chain (Sw12 ∷ Toff023 ∷ Sw12 ∷ []) (Sw12 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 2 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 3 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 4 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 5 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw12 ∷ []) (K0 ∷ Sw12 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ Sw12 ∷ [])
  b1 = at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 8 2 (ι ∷ Sw01 ∷ []) wn00122 ▸
       at 9 2 [] wn00031 ▸
       at 0 2 (K0 ∷ Sw12 ∷ []) (sym (low₁-comm (K) (Swap))) ▸ done

  b2 : Chain (K0 ∷ Sw12 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ Sw12 ∷ []) (K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw12 ∷ [])
  b2 = at 1 2 (CS13 ∷ Sw12 ∷ []) wn00049 ▸
       at 3 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00014 ▸
       at 3 2 (CS13⁻ ∷ Sw12 ∷ []) wn00051 ▸
       at 5 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00014 ▸
       at 6 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) wn00022 ▸ done

  b3 : Chain (K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw12 ∷ []) (Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw12 ∷ [])
  b3 = at 7 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 8 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) wn00023 ▸
       at 5 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K0 ∷ Sw12 ∷ []) (sym (low₁-comm (K) (Swap))) ▸
       at 7 2 (ι ∷ Sw12 ∷ []) (sym (low₁-comm (iI) (Swap))) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw12 ∷ []) (Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ Sw23 ∷ ι ∷ Sw12 ∷ Sw12 ∷ [])
  b4 = at 2 2 [] wn00003 ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸
       at 7 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸ done

  b5 : Chain (Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ Sw23 ∷ ι ∷ Sw12 ∷ Sw12 ∷ []) (Toff013 ∷ [])
  b5 = at 8 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 1 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) wn00056 ▸
       at 1 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 TOFF102: 15 steps
lem-sw1-TOFF102 : ⟪ (Sw12 ∷ Toff102 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ []) ⟫ʷ
lem-sw1-TOFF102 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw12 ∷ Toff102 ∷ Sw12 ∷ []) (K2 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ Sw12 ∷ CS02 ∷ K1 ∷ ι ∷ Sw12 ∷ [])
  b0 = at 1 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (K2 ∷ Sw12 ∷ []) wn00340 ▸
       at 1 2 (CS12 ∷ Sw12 ∷ []) wn00018 ▸
       at 4 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 2 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS12⁻ ∷ Sw12 ∷ []) wn00019 ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (K2 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ Sw12 ∷ CS02 ∷ K1 ∷ ι ∷ Sw12 ∷ []) (Toff201 ∷ [])
  b1 = at 6 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00014 ▸
       at 6 2 (K2 ∷ Sw12 ∷ []) wn00340 ▸
       at 7 2 (ι ∷ Sw12 ∷ []) (sym (low₁-comm (iI) (Swap))) ▸
       at 0 8 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) wn00363 ▸
       at 0 8 (Toff201 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00014 ▸ done

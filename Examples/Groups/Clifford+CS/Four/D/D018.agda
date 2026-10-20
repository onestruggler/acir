{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D018 where

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
open import Examples.Groups.Clifford+CS.Four.Wins.W01 using (wn00001 ; wn00003 ; wn00005 ; wn00012 ; wn00014 ; wn00018 ; wn00019 ; wn00020 ; wn00021 ; wn00022 ; wn00023 ; wn00024 ; wn00025 ; wn00027 ; wn00030 ; wn00031 ; wn00043 ; wn00049 ; wn00050 ; wn00051 ; wn00056 ; wn00071 ; wn00072 ; wn00073 ; wn00121 ; wn00122 ; wn00123 ; wn00124 ; wn00151 ; wn00153 ; wn00175 ; wn00196)
open import Examples.Groups.Clifford+CS.Four.Wins.W02 using (wn00334 ; wn00335 ; wn00336 ; wn00337 ; wn00340 ; wn00345 ; wn00364 ; wn00365 ; wn00366 ; wn00367 ; wn00368 ; wn00369 ; wn00370 ; wn00371 ; wn00372 ; wn00373 ; wn00374 ; wn00375 ; wn00376 ; wn00377 ; wn00378 ; wn00379 ; wn00380 ; wn00381 ; wn00382 ; wn00383 ; wn00384 ; wn00385)

-- sw1 TOFF103: 45 steps
lem-sw1-TOFF103 : ⟪ (Sw12 ∷ Toff103 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ []) ⟫ʷ
lem-sw1-TOFF103 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (run b5)))))
  where
  b0 : Chain (Sw12 ∷ Toff103 ∷ Sw12 ∷ []) (Sw12 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw12 ∷ []) (K2 ∷ CS23 ∷ Sw12 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw12 ∷ [])
  b1 = at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 9 2 [] wn00003 ▸
       at 0 2 (K2 ∷ Sw12 ∷ []) wn00340 ▸
       at 1 2 (CS23 ∷ Sw12 ∷ []) wn00020 ▸ done

  b2 : Chain (K2 ∷ CS23 ∷ Sw12 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw12 ∷ []) (K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ K1 ∷ ι ∷ Sw12 ∷ [])
  b2 = at 4 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 2 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS23⁻ ∷ Sw12 ∷ []) wn00021 ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) wn00022 ▸
       at 7 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸ done

  b3 : Chain (K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ K1 ∷ ι ∷ Sw12 ∷ []) (Sw01 ∷ K2 ∷ CS23 ∷ CX12 ∷ Sw01 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ Sw12 ∷ Sw12 ∷ [])
  b3 = at 8 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) wn00023 ▸
       at 5 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K2 ∷ Sw12 ∷ []) wn00340 ▸
       at 7 2 (ι ∷ Sw12 ∷ []) (sym (low₁-comm (iI) (Swap))) ▸
       at 0 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 1 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 2 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 3 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸ done

  b4 : Chain (Sw01 ∷ K2 ∷ CS23 ∷ CX12 ∷ Sw01 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ Sw12 ∷ Sw12 ∷ []) (Sw01 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ Sw01 ∷ ι ∷ Sw12 ∷ Sw12 ∷ [])
  b4 = at 4 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 5 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸ done

  b5 : Chain (Sw01 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ Sw01 ∷ ι ∷ Sw12 ∷ Sw12 ∷ []) (Toff203 ∷ [])
  b5 = at 8 2 (ι1 ∷ Sw01 ∷ []) wn00124 ▸
       at 1 8 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) wn00334 ▸
       at 1 8 (Toff213 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff203 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 TOFF123: 12 steps
lem-sw1-TOFF123 : ⟪ (Sw12 ∷ Toff123 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ []) ⟫ʷ
lem-sw1-TOFF123 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw12 ∷ Toff123 ∷ Sw12 ∷ []) (K2 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ K2 ∷ Sw12 ∷ ι1 ∷ Sw12 ∷ [])
  b0 = at 1 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (K2 ∷ Sw12 ∷ []) wn00340 ▸
       at 1 2 (CS13 ∷ Sw12 ∷ []) wn00049 ▸
       at 2 2 (CX21 ∷ Sw12 ∷ []) wn00050 ▸
       at 3 2 (CS13⁻ ∷ Sw12 ∷ []) wn00051 ▸
       at 4 2 (CX21 ∷ Sw12 ∷ []) wn00050 ▸
       at 5 2 (CS23 ∷ Sw12 ∷ []) wn00020 ▸
       at 6 2 (K2 ∷ Sw12 ∷ []) wn00340 ▸ done

  b1 : Chain (K2 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ K2 ∷ Sw12 ∷ ι1 ∷ Sw12 ∷ []) (Toff213 ∷ [])
  b1 = at 7 2 (ι2 ∷ Sw12 ∷ []) wn00364 ▸
       at 0 8 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) wn00365 ▸
       at 0 8 (Toff213 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 TOFF201: 15 steps
lem-sw1-TOFF201 : ⟪ (Sw12 ∷ Toff201 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ []) ⟫ʷ
lem-sw1-TOFF201 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw12 ∷ Toff201 ∷ Sw12 ∷ []) (K1 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ Sw12 ∷ CS02 ∷ K2 ∷ ι ∷ Sw12 ∷ [])
  b0 = at 1 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (K1 ∷ Sw12 ∷ []) wn00345 ▸
       at 1 2 (CS12 ∷ Sw12 ∷ []) wn00018 ▸
       at 4 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 2 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS12⁻ ∷ Sw12 ∷ []) wn00019 ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (K1 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ Sw12 ∷ CS02 ∷ K2 ∷ ι ∷ Sw12 ∷ []) (Toff102 ∷ [])
  b1 = at 6 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00014 ▸
       at 6 2 (K1 ∷ Sw12 ∷ []) wn00345 ▸
       at 7 2 (ι ∷ Sw12 ∷ []) (sym (low₁-comm (iI) (Swap))) ▸
       at 0 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) wn00366 ▸
       at 0 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 TOFF203: 45 steps
lem-sw1-TOFF203 : ⟪ (Sw12 ∷ Toff203 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ []) ⟫ʷ
lem-sw1-TOFF203 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (run b5)))))
  where
  b0 : Chain (Sw12 ∷ Toff203 ∷ Sw12 ∷ []) (Sw12 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ K2 ∷ ι1 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw01 ∷ Toff213 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 2 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 3 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 4 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 5 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ K2 ∷ ι1 ∷ Sw01 ∷ Sw12 ∷ []) (K1 ∷ Sw12 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ Sw12 ∷ [])
  b1 = at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 8 2 (ι ∷ Sw01 ∷ []) wn00122 ▸
       at 9 2 [] wn00031 ▸
       at 0 2 (K1 ∷ Sw12 ∷ []) wn00345 ▸ done

  b2 : Chain (K1 ∷ Sw12 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ Sw12 ∷ []) (K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ K2 ∷ ι ∷ Sw12 ∷ [])
  b2 = at 1 2 (CS13 ∷ Sw12 ∷ []) wn00049 ▸
       at 3 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00014 ▸
       at 3 2 (CS13⁻ ∷ Sw12 ∷ []) wn00051 ▸
       at 5 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00014 ▸
       at 6 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) wn00022 ▸ done

  b3 : Chain (K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ K2 ∷ ι ∷ Sw12 ∷ []) (Sw23 ∷ K1 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw12 ∷ [])
  b3 = at 7 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 8 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) wn00023 ▸
       at 5 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K1 ∷ Sw12 ∷ []) wn00345 ▸
       at 7 2 (ι ∷ Sw12 ∷ []) (sym (low₁-comm (iI) (Swap))) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (Sw23 ∷ K1 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw12 ∷ []) (Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ Sw23 ∷ ι ∷ Sw12 ∷ Sw12 ∷ [])
  b4 = at 2 2 [] wn00003 ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸
       at 7 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸ done

  b5 : Chain (Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ Sw23 ∷ ι ∷ Sw12 ∷ Sw12 ∷ []) (Toff103 ∷ [])
  b5 = at 8 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 1 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) wn00196 ▸
       at 1 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff103 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 TOFF213: 12 steps
lem-sw1-TOFF213 : ⟪ (Sw12 ∷ Toff213 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Toff123 ∷ []) ⟫ʷ
lem-sw1-TOFF213 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw12 ∷ Toff213 ∷ Sw12 ∷ []) (K1 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ K1 ∷ Sw12 ∷ ι1 ∷ Sw12 ∷ [])
  b0 = at 1 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (K1 ∷ Sw12 ∷ []) wn00345 ▸
       at 1 2 (CS13 ∷ Sw12 ∷ []) wn00049 ▸
       at 2 2 (CX21 ∷ Sw12 ∷ []) wn00050 ▸
       at 3 2 (CS13⁻ ∷ Sw12 ∷ []) wn00051 ▸
       at 4 2 (CX21 ∷ Sw12 ∷ []) wn00050 ▸
       at 5 2 (CS23 ∷ Sw12 ∷ []) wn00020 ▸
       at 6 2 (K1 ∷ Sw12 ∷ []) wn00345 ▸ done

  b1 : Chain (K1 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ K1 ∷ Sw12 ∷ ι1 ∷ Sw12 ∷ []) (Toff123 ∷ [])
  b1 = at 7 2 (ι2 ∷ Sw12 ∷ []) wn00364 ▸
       at 0 8 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) wn00367 ▸
       at 0 8 (Toff123 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 TOFF301: 45 steps
lem-sw1-TOFF301 : ⟪ (Sw12 ∷ Toff301 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ []) ⟫ʷ
lem-sw1-TOFF301 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (run b5)))))
  where
  b0 : Chain (Sw12 ∷ Toff301 ∷ Sw12 ∷ []) (Sw12 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (K3 ∷ Sw23 ∷ []) wn00335 ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw12 ∷ []) (K3 ∷ CS23 ∷ Sw12 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw12 ∷ [])
  b1 = at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K3 ∷ Sw23 ∷ []) wn00335 ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 9 2 [] wn00003 ▸
       at 0 2 (K3 ∷ Sw12 ∷ []) (low₃-comm ((Swap ↑)) (K)) ▸
       at 1 2 (CS23 ∷ Sw12 ∷ []) wn00020 ▸ done

  b2 : Chain (K3 ∷ CS23 ∷ Sw12 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw12 ∷ []) (K3 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ K3 ∷ ι ∷ Sw12 ∷ [])
  b2 = at 4 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 2 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS23⁻ ∷ Sw12 ∷ []) wn00021 ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) wn00022 ▸
       at 7 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸ done

  b3 : Chain (K3 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ K3 ∷ ι ∷ Sw12 ∷ []) (Sw01 ∷ K3 ∷ CS23 ∷ CX12 ∷ Sw01 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K3 ∷ ι ∷ Sw12 ∷ Sw12 ∷ [])
  b3 = at 8 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) wn00023 ▸
       at 5 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K3 ∷ Sw12 ∷ []) (low₃-comm ((Swap ↑)) (K)) ▸
       at 7 2 (ι ∷ Sw12 ∷ []) (sym (low₁-comm (iI) (Swap))) ▸
       at 0 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 1 2 (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑))) ▸
       at 2 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 3 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸ done

  b4 : Chain (Sw01 ∷ K3 ∷ CS23 ∷ CX12 ∷ Sw01 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K3 ∷ ι ∷ Sw12 ∷ Sw12 ∷ []) (Sw01 ∷ K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ Sw01 ∷ ι ∷ Sw12 ∷ Sw12 ∷ [])
  b4 = at 4 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 5 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑))) ▸ done

  b5 : Chain (Sw01 ∷ K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ Sw01 ∷ ι ∷ Sw12 ∷ Sw12 ∷ []) (Toff302 ∷ [])
  b5 = at 8 2 (ι1 ∷ Sw01 ∷ []) wn00124 ▸
       at 1 8 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) wn00337 ▸
       at 1 8 (Toff312 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff302 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 TOFF302: 45 steps
lem-sw1-TOFF302 : ⟪ (Sw12 ∷ Toff302 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ []) ⟫ʷ
lem-sw1-TOFF302 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (run b5)))))
  where
  b0 : Chain (Sw12 ∷ Toff302 ∷ Sw12 ∷ []) (Sw12 ∷ K3 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ K3 ∷ ι1 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw01 ∷ Toff312 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑))) ▸
       at 2 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 3 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 4 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 5 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ K3 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ K3 ∷ ι1 ∷ Sw01 ∷ Sw12 ∷ []) (K3 ∷ Sw12 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K3 ∷ ι ∷ Sw12 ∷ [])
  b1 = at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑))) ▸
       at 8 2 (ι ∷ Sw01 ∷ []) wn00122 ▸
       at 9 2 [] wn00031 ▸
       at 0 2 (K3 ∷ Sw12 ∷ []) (low₃-comm ((Swap ↑)) (K)) ▸ done

  b2 : Chain (K3 ∷ Sw12 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K3 ∷ ι ∷ Sw12 ∷ []) (K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ K3 ∷ ι ∷ Sw12 ∷ [])
  b2 = at 1 2 (CS13 ∷ Sw12 ∷ []) wn00049 ▸
       at 3 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00014 ▸
       at 3 2 (CS13⁻ ∷ Sw12 ∷ []) wn00051 ▸
       at 5 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00014 ▸
       at 6 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) wn00022 ▸ done

  b3 : Chain (K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ K3 ∷ ι ∷ Sw12 ∷ []) (Sw23 ∷ K2 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw12 ∷ Sw12 ∷ [])
  b3 = at 7 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 8 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) wn00023 ▸
       at 5 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K3 ∷ Sw12 ∷ []) (low₃-comm ((Swap ↑)) (K)) ▸
       at 7 2 (ι ∷ Sw12 ∷ []) (sym (low₁-comm (iI) (Swap))) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 2 (K2 ∷ Sw23 ∷ []) wn00336 ▸
       at 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (Sw23 ∷ K2 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw12 ∷ Sw12 ∷ []) (Sw23 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ Sw23 ∷ ι ∷ Sw12 ∷ Sw12 ∷ [])
  b4 = at 2 2 [] wn00003 ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸
       at 7 2 (K2 ∷ Sw23 ∷ []) wn00336 ▸ done

  b5 : Chain (Sw23 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ Sw23 ∷ ι ∷ Sw12 ∷ Sw12 ∷ []) (Toff301 ∷ [])
  b5 = at 8 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 1 8 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) wn00368 ▸
       at 1 8 (Toff201 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff301 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00014 ▸ done

-- sw1 TOFF312: 12 steps
lem-sw1-TOFF312 : ⟪ (Sw12 ∷ Toff312 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ []) ⟫ʷ
lem-sw1-TOFF312 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw12 ∷ Toff312 ∷ Sw12 ∷ []) (K3 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ K3 ∷ Sw12 ∷ ι1 ∷ Sw12 ∷ [])
  b0 = at 1 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (K3 ∷ Sw12 ∷ []) (low₃-comm ((Swap ↑)) (K)) ▸
       at 1 2 (CS13 ∷ Sw12 ∷ []) wn00049 ▸
       at 2 2 (CX21 ∷ Sw12 ∷ []) wn00050 ▸
       at 3 2 (CS13⁻ ∷ Sw12 ∷ []) wn00051 ▸
       at 4 2 (CX21 ∷ Sw12 ∷ []) wn00050 ▸
       at 5 2 (CS23 ∷ Sw12 ∷ []) wn00020 ▸
       at 6 2 (K3 ∷ Sw12 ∷ []) (low₃-comm ((Swap ↑)) (K)) ▸ done

  b1 : Chain (K3 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ K3 ∷ Sw12 ∷ ι1 ∷ Sw12 ∷ []) (Toff312 ∷ [])
  b1 = at 7 2 (ι2 ∷ Sw12 ∷ []) wn00364 ▸
       at 0 8 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) wn00369 ▸
       at 0 8 (Toff312 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00014 ▸ done

-- sw2 S0: 2 steps
lem-sw2-S0 : ⟪ (Sw23 ∷ S0 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ []) ⟫ʷ
lem-sw2-S0 = run b0
  where
  b0 : Chain (Sw23 ∷ S0 ∷ Sw23 ∷ []) (S0 ∷ [])
  b0 = at 0 2 (S0 ∷ Sw23 ∷ []) (sym (low₁-comm (S) ((Swap ↑)))) ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 Sd0: 2 steps
lem-sw2-Sd0 : ⟪ (Sw23 ∷ S0⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ []) ⟫ʷ
lem-sw2-Sd0 = run b0
  where
  b0 : Chain (Sw23 ∷ S0⁻ ∷ Sw23 ∷ []) (S0⁻ ∷ [])
  b0 = at 0 2 (S0⁻ ∷ Sw23 ∷ []) (sym (low₁-comm ((S • S • S)) ((Swap ↑)))) ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 K0: 2 steps
lem-sw2-K0 : ⟪ (Sw23 ∷ K0 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ []) ⟫ʷ
lem-sw2-K0 = run b0
  where
  b0 : Chain (Sw23 ∷ K0 ∷ Sw23 ∷ []) (K0 ∷ [])
  b0 = at 0 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 Kd0: 2 steps
lem-sw2-Kd0 : ⟪ (Sw23 ∷ K0⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ []) ⟫ʷ
lem-sw2-Kd0 = run b0
  where
  b0 : Chain (Sw23 ∷ K0⁻ ∷ Sw23 ∷ []) (K0⁻ ∷ [])
  b0 = at 0 2 (K0⁻ ∷ Sw23 ∷ []) (sym (low₁-comm ((K • iI)) ((Swap ↑)))) ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 X0: 2 steps
lem-sw2-X0 : ⟪ (Sw23 ∷ X0 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ []) ⟫ʷ
lem-sw2-X0 = run b0
  where
  b0 : Chain (Sw23 ∷ X0 ∷ Sw23 ∷ []) (X0 ∷ [])
  b0 = at 0 2 (X0 ∷ Sw23 ∷ []) (sym (low₁-comm (X) ((Swap ↑)))) ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 Z0: 2 steps
lem-sw2-Z0 : ⟪ (Sw23 ∷ Z0 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Z0 ∷ []) ⟫ʷ
lem-sw2-Z0 = run b0
  where
  b0 : Chain (Sw23 ∷ Z0 ∷ Sw23 ∷ []) (Z0 ∷ [])
  b0 = at 0 2 (Z0 ∷ Sw23 ∷ []) (sym (low₁-comm (Z) ((Swap ↑)))) ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 S1: 2 steps
lem-sw2-S1 : ⟪ (Sw23 ∷ S1 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ []) ⟫ʷ
lem-sw2-S1 = run b0
  where
  b0 : Chain (Sw23 ∷ S1 ∷ Sw23 ∷ []) (S1 ∷ [])
  b0 = at 0 2 (S1 ∷ Sw23 ∷ []) (sym (low-comm ((S ↑)) (Swap))) ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 Sd1: 2 steps
lem-sw2-Sd1 : ⟪ (Sw23 ∷ S1⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ []) ⟫ʷ
lem-sw2-Sd1 = run b0
  where
  b0 : Chain (Sw23 ∷ S1⁻ ∷ Sw23 ∷ []) (S1⁻ ∷ [])
  b0 = at 0 2 (S1⁻ ∷ Sw23 ∷ []) (sym (low-comm (((S • S • S) ↑)) (Swap))) ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 K1: 2 steps
lem-sw2-K1 : ⟪ (Sw23 ∷ K1 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ []) ⟫ʷ
lem-sw2-K1 = run b0
  where
  b0 : Chain (Sw23 ∷ K1 ∷ Sw23 ∷ []) (K1 ∷ [])
  b0 = at 0 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 Kd1: 2 steps
lem-sw2-Kd1 : ⟪ (Sw23 ∷ K1⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (K1⁻ ∷ []) ⟫ʷ
lem-sw2-Kd1 = run b0
  where
  b0 : Chain (Sw23 ∷ K1⁻ ∷ Sw23 ∷ []) (K1⁻ ∷ [])
  b0 = at 0 2 (K1⁻ ∷ Sw23 ∷ []) (sym (low-comm (((K • iI) ↑)) (Swap))) ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 X1: 2 steps
lem-sw2-X1 : ⟪ (Sw23 ∷ X1 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ []) ⟫ʷ
lem-sw2-X1 = run b0
  where
  b0 : Chain (Sw23 ∷ X1 ∷ Sw23 ∷ []) (X1 ∷ [])
  b0 = at 0 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 Z1: 2 steps
lem-sw2-Z1 : ⟪ (Sw23 ∷ Z1 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Z1 ∷ []) ⟫ʷ
lem-sw2-Z1 = run b0
  where
  b0 : Chain (Sw23 ∷ Z1 ∷ Sw23 ∷ []) (Z1 ∷ [])
  b0 = at 0 2 (Z1 ∷ Sw23 ∷ []) (sym (low-comm ((Z ↑)) (Swap))) ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 S2: 2 steps
lem-sw2-S2 : ⟪ (Sw23 ∷ S2 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (S3 ∷ []) ⟫ʷ
lem-sw2-S2 = run b0
  where
  b0 : Chain (Sw23 ∷ S2 ∷ Sw23 ∷ []) (S3 ∷ [])
  b0 = at 0 2 (S3 ∷ Sw23 ∷ []) wn00151 ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 Sd2: 2 steps
lem-sw2-Sd2 : ⟪ (Sw23 ∷ S2⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (S3⁻ ∷ []) ⟫ʷ
lem-sw2-Sd2 = run b0
  where
  b0 : Chain (Sw23 ∷ S2⁻ ∷ Sw23 ∷ []) (S3⁻ ∷ [])
  b0 = at 0 2 (S3⁻ ∷ Sw23 ∷ []) wn00153 ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 K2: 2 steps
lem-sw2-K2 : ⟪ (Sw23 ∷ K2 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (K3 ∷ []) ⟫ʷ
lem-sw2-K2 = run b0
  where
  b0 : Chain (Sw23 ∷ K2 ∷ Sw23 ∷ []) (K3 ∷ [])
  b0 = at 0 2 (K3 ∷ Sw23 ∷ []) wn00335 ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 Kd2: 2 steps
lem-sw2-Kd2 : ⟪ (Sw23 ∷ K2⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (K3⁻ ∷ []) ⟫ʷ
lem-sw2-Kd2 = run b0
  where
  b0 : Chain (Sw23 ∷ K2⁻ ∷ Sw23 ∷ []) (K3⁻ ∷ [])
  b0 = at 0 2 (K3⁻ ∷ Sw23 ∷ []) wn00370 ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 X2: 2 steps
lem-sw2-X2 : ⟪ (Sw23 ∷ X2 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ []) ⟫ʷ
lem-sw2-X2 = run b0
  where
  b0 : Chain (Sw23 ∷ X2 ∷ Sw23 ∷ []) (X3 ∷ [])
  b0 = at 0 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 Z2: 2 steps
lem-sw2-Z2 : ⟪ (Sw23 ∷ Z2 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Z3 ∷ []) ⟫ʷ
lem-sw2-Z2 = run b0
  where
  b0 : Chain (Sw23 ∷ Z2 ∷ Sw23 ∷ []) (Z3 ∷ [])
  b0 = at 0 2 (Z3 ∷ Sw23 ∷ []) wn00371 ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 S3: 2 steps
lem-sw2-S3 : ⟪ (Sw23 ∷ S3 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (S2 ∷ []) ⟫ʷ
lem-sw2-S3 = run b0
  where
  b0 : Chain (Sw23 ∷ S3 ∷ Sw23 ∷ []) (S2 ∷ [])
  b0 = at 0 2 (S2 ∷ Sw23 ∷ []) wn00372 ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 Sd3: 2 steps
lem-sw2-Sd3 : ⟪ (Sw23 ∷ S3⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (S2⁻ ∷ []) ⟫ʷ
lem-sw2-Sd3 = run b0
  where
  b0 : Chain (Sw23 ∷ S3⁻ ∷ Sw23 ∷ []) (S2⁻ ∷ [])
  b0 = at 0 2 (S2⁻ ∷ Sw23 ∷ []) wn00373 ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 K3: 2 steps
lem-sw2-K3 : ⟪ (Sw23 ∷ K3 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ []) ⟫ʷ
lem-sw2-K3 = run b0
  where
  b0 : Chain (Sw23 ∷ K3 ∷ Sw23 ∷ []) (K2 ∷ [])
  b0 = at 0 2 (K2 ∷ Sw23 ∷ []) wn00336 ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 Kd3: 2 steps
lem-sw2-Kd3 : ⟪ (Sw23 ∷ K3⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (K2⁻ ∷ []) ⟫ʷ
lem-sw2-Kd3 = run b0
  where
  b0 : Chain (Sw23 ∷ K3⁻ ∷ Sw23 ∷ []) (K2⁻ ∷ [])
  b0 = at 0 2 (K2⁻ ∷ Sw23 ∷ []) wn00374 ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 X3: 2 steps
lem-sw2-X3 : ⟪ (Sw23 ∷ X3 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ []) ⟫ʷ
lem-sw2-X3 = run b0
  where
  b0 : Chain (Sw23 ∷ X3 ∷ Sw23 ∷ []) (X2 ∷ [])
  b0 = at 0 2 (X2 ∷ Sw23 ∷ []) wn00375 ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 Z3: 2 steps
lem-sw2-Z3 : ⟪ (Sw23 ∷ Z3 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Z2 ∷ []) ⟫ʷ
lem-sw2-Z3 = run b0
  where
  b0 : Chain (Sw23 ∷ Z3 ∷ Sw23 ∷ []) (Z2 ∷ [])
  b0 = at 0 2 (Z2 ∷ Sw23 ∷ []) wn00376 ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 CS01: 2 steps
lem-sw2-CS01 : ⟪ (Sw23 ∷ CS01 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ []) ⟫ʷ
lem-sw2-CS01 = run b0
  where
  b0 : Chain (Sw23 ∷ CS01 ∷ Sw23 ∷ []) (CS01 ∷ [])
  b0 = at 0 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 CSd01: 2 steps
lem-sw2-CSd01 : ⟪ (Sw23 ∷ CS01⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ []) ⟫ʷ
lem-sw2-CSd01 = run b0
  where
  b0 : Chain (Sw23 ∷ CS01⁻ ∷ Sw23 ∷ []) (CS01⁻ ∷ [])
  b0 = at 0 2 (CS01⁻ ∷ Sw23 ∷ []) (sym (low-comm ((CS • CS • CS)) (Swap))) ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 CZ01: 2 steps
lem-sw2-CZ01 : ⟪ (Sw23 ∷ CZ01 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CZ01 ∷ []) ⟫ʷ
lem-sw2-CZ01 = run b0
  where
  b0 : Chain (Sw23 ∷ CZ01 ∷ Sw23 ∷ []) (CZ01 ∷ [])
  b0 = at 0 2 (CZ01 ∷ Sw23 ∷ []) (sym (low-comm (CZ) (Swap))) ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 CX01: 2 steps
lem-sw2-CX01 : ⟪ (Sw23 ∷ CX01 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CX01 ∷ []) ⟫ʷ
lem-sw2-CX01 = run b0
  where
  b0 : Chain (Sw23 ∷ CX01 ∷ Sw23 ∷ []) (CX01 ∷ [])
  b0 = at 0 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 CK01: 2 steps
lem-sw2-CK01 : ⟪ (Sw23 ∷ CK01 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK01 ∷ []) ⟫ʷ
lem-sw2-CK01 = run b0
  where
  b0 : Chain (Sw23 ∷ CK01 ∷ Sw23 ∷ []) (CK01 ∷ [])
  b0 = at 0 2 (CK01 ∷ Sw23 ∷ []) (sym (low-comm (CK₀₁) (Swap))) ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 CKd01: 2 steps
lem-sw2-CKd01 : ⟪ (Sw23 ∷ CK01⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK01⁻ ∷ []) ⟫ʷ
lem-sw2-CKd01 = run b0
  where
  b0 : Chain (Sw23 ∷ CK01⁻ ∷ Sw23 ∷ []) (CK01⁻ ∷ [])
  b0 = at 0 2 (CK01⁻ ∷ Sw23 ∷ []) (sym (low-comm ((S • CK₀₁)) (Swap))) ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 CS02: 3 steps
lem-sw2-CS02 : ⟪ (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ []) ⟫ʷ
lem-sw2-CS02 = run b0
  where
  b0 : Chain (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (CS03 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 0 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 CSd02: 3 steps
lem-sw2-CSd02 : ⟪ (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ []) ⟫ʷ
lem-sw2-CSd02 = run b0
  where
  b0 : Chain (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (CS03⁻ ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 0 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 CZ02: 3 steps
lem-sw2-CZ02 : ⟪ (Sw23 ∷ CZ02 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CZ03 ∷ []) ⟫ʷ
lem-sw2-CZ02 = run b0
  where
  b0 : Chain (Sw23 ∷ CZ02 ∷ Sw23 ∷ []) (CZ03 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 0 3 (CZ03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 CX02: 3 steps
lem-sw2-CX02 : ⟪ (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CX03 ∷ []) ⟫ʷ
lem-sw2-CX02 = run b0
  where
  b0 : Chain (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (CX03 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 0 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 CK02: 3 steps
lem-sw2-CK02 : ⟪ (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK03 ∷ []) ⟫ʷ
lem-sw2-CK02 = run b0
  where
  b0 : Chain (Sw23 ∷ CK02 ∷ Sw23 ∷ []) (CK03 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 0 3 (CK03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 CKd02: 3 steps
lem-sw2-CKd02 : ⟪ (Sw23 ∷ CK02⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK03⁻ ∷ []) ⟫ʷ
lem-sw2-CKd02 = run b0
  where
  b0 : Chain (Sw23 ∷ CK02⁻ ∷ Sw23 ∷ []) (CK03⁻ ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 0 3 (CK03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 CS03: 3 steps
lem-sw2-CS03 : ⟪ (Sw23 ∷ CS03 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ []) ⟫ʷ
lem-sw2-CS03 = run b0
  where
  b0 : Chain (Sw23 ∷ CS03 ∷ Sw23 ∷ []) (CS02 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] wn00003 ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 CSd03: 3 steps
lem-sw2-CSd03 : ⟪ (Sw23 ∷ CS03⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ []) ⟫ʷ
lem-sw2-CSd03 = run b0
  where
  b0 : Chain (Sw23 ∷ CS03⁻ ∷ Sw23 ∷ []) (CS02⁻ ∷ [])
  b0 = at 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] wn00003 ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 CZ03: 3 steps
lem-sw2-CZ03 : ⟪ (Sw23 ∷ CZ03 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CZ02 ∷ []) ⟫ʷ
lem-sw2-CZ03 = run b0
  where
  b0 : Chain (Sw23 ∷ CZ03 ∷ Sw23 ∷ []) (CZ02 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CZ02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] wn00003 ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 CX03: 3 steps
lem-sw2-CX03 : ⟪ (Sw23 ∷ CX03 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CX02 ∷ []) ⟫ʷ
lem-sw2-CX03 = run b0
  where
  b0 : Chain (Sw23 ∷ CX03 ∷ Sw23 ∷ []) (CX02 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] wn00003 ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 CK03: 3 steps
lem-sw2-CK03 : ⟪ (Sw23 ∷ CK03 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK02 ∷ []) ⟫ʷ
lem-sw2-CK03 = run b0
  where
  b0 : Chain (Sw23 ∷ CK03 ∷ Sw23 ∷ []) (CK02 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] wn00003 ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 CKd03: 3 steps
lem-sw2-CKd03 : ⟪ (Sw23 ∷ CK03⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK02⁻ ∷ []) ⟫ʷ
lem-sw2-CKd03 = run b0
  where
  b0 : Chain (Sw23 ∷ CK03⁻ ∷ Sw23 ∷ []) (CK02⁻ ∷ [])
  b0 = at 1 1 (Sw23 ∷ CK02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] wn00003 ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 CX10: 2 steps
lem-sw2-CX10 : ⟪ (Sw23 ∷ CX10 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CX10 ∷ []) ⟫ʷ
lem-sw2-CX10 = run b0
  where
  b0 : Chain (Sw23 ∷ CX10 ∷ Sw23 ∷ []) (CX10 ∷ [])
  b0 = at 0 2 (CX10 ∷ Sw23 ∷ []) (sym (low-comm (CX₁₀) (Swap))) ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 CK10: 2 steps
lem-sw2-CK10 : ⟪ (Sw23 ∷ CK10 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK10 ∷ []) ⟫ʷ
lem-sw2-CK10 = run b0
  where
  b0 : Chain (Sw23 ∷ CK10 ∷ Sw23 ∷ []) (CK10 ∷ [])
  b0 = at 0 2 (CK10 ∷ Sw23 ∷ []) (sym (low-comm (CK₁₀) (Swap))) ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 CKd10: 2 steps
lem-sw2-CKd10 : ⟪ (Sw23 ∷ CK10⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK10⁻ ∷ []) ⟫ʷ
lem-sw2-CKd10 = run b0
  where
  b0 : Chain (Sw23 ∷ CK10⁻ ∷ Sw23 ∷ []) (CK10⁻ ∷ [])
  b0 = at 0 2 (CK10⁻ ∷ Sw23 ∷ []) (sym (low-comm ((S ↑ • CK₁₀)) (Swap))) ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 CS12: 3 steps
lem-sw2-CS12 : ⟪ (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ []) ⟫ʷ
lem-sw2-CS12 = run b0
  where
  b0 : Chain (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (CS13 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 0 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 CSd12: 3 steps
lem-sw2-CSd12 : ⟪ (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ []) ⟫ʷ
lem-sw2-CSd12 = run b0
  where
  b0 : Chain (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (CS13⁻ ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 0 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 CZ12: 3 steps
lem-sw2-CZ12 : ⟪ (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CZ13 ∷ []) ⟫ʷ
lem-sw2-CZ12 = run b0
  where
  b0 : Chain (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (CZ13 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 0 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 CX12: 3 steps
lem-sw2-CX12 : ⟪ (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CX13 ∷ []) ⟫ʷ
lem-sw2-CX12 = run b0
  where
  b0 : Chain (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (CX13 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 0 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 CK12: 3 steps
lem-sw2-CK12 : ⟪ (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK13 ∷ []) ⟫ʷ
lem-sw2-CK12 = run b0
  where
  b0 : Chain (Sw23 ∷ CK12 ∷ Sw23 ∷ []) (CK13 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 0 3 (CK13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 CKd12: 3 steps
lem-sw2-CKd12 : ⟪ (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK13⁻ ∷ []) ⟫ʷ
lem-sw2-CKd12 = run b0
  where
  b0 : Chain (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) (CK13⁻ ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 0 3 (CK13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 CS13: 3 steps
lem-sw2-CS13 : ⟪ (Sw23 ∷ CS13 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ []) ⟫ʷ
lem-sw2-CS13 = run b0
  where
  b0 : Chain (Sw23 ∷ CS13 ∷ Sw23 ∷ []) (CS12 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] wn00003 ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 CSd13: 3 steps
lem-sw2-CSd13 : ⟪ (Sw23 ∷ CS13⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ []) ⟫ʷ
lem-sw2-CSd13 = run b0
  where
  b0 : Chain (Sw23 ∷ CS13⁻ ∷ Sw23 ∷ []) (CS12⁻ ∷ [])
  b0 = at 1 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] wn00003 ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 CZ13: 3 steps
lem-sw2-CZ13 : ⟪ (Sw23 ∷ CZ13 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CZ12 ∷ []) ⟫ʷ
lem-sw2-CZ13 = run b0
  where
  b0 : Chain (Sw23 ∷ CZ13 ∷ Sw23 ∷ []) (CZ12 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] wn00003 ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 CX13: 3 steps
lem-sw2-CX13 : ⟪ (Sw23 ∷ CX13 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CX12 ∷ []) ⟫ʷ
lem-sw2-CX13 = run b0
  where
  b0 : Chain (Sw23 ∷ CX13 ∷ Sw23 ∷ []) (CX12 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] wn00003 ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 CK13: 3 steps
lem-sw2-CK13 : ⟪ (Sw23 ∷ CK13 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK12 ∷ []) ⟫ʷ
lem-sw2-CK13 = run b0
  where
  b0 : Chain (Sw23 ∷ CK13 ∷ Sw23 ∷ []) (CK12 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] wn00003 ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 CKd13: 3 steps
lem-sw2-CKd13 : ⟪ (Sw23 ∷ CK13⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK12⁻ ∷ []) ⟫ʷ
lem-sw2-CKd13 = run b0
  where
  b0 : Chain (Sw23 ∷ CK13⁻ ∷ Sw23 ∷ []) (CK12⁻ ∷ [])
  b0 = at 1 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] wn00003 ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 CX20: 3 steps
lem-sw2-CX20 : ⟪ (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CX30 ∷ []) ⟫ʷ
lem-sw2-CX20 = run b0
  where
  b0 : Chain (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (CX30 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 0 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 CK20: 3 steps
lem-sw2-CK20 : ⟪ (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK30 ∷ []) ⟫ʷ
lem-sw2-CK20 = run b0
  where
  b0 : Chain (Sw23 ∷ CK20 ∷ Sw23 ∷ []) (CK30 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 0 3 (CK30 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 CKd20: 3 steps
lem-sw2-CKd20 : ⟪ (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK30⁻ ∷ []) ⟫ʷ
lem-sw2-CKd20 = run b0
  where
  b0 : Chain (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) (CK30⁻ ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 0 3 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 CX21: 3 steps
lem-sw2-CX21 : ⟪ (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CX31 ∷ []) ⟫ʷ
lem-sw2-CX21 = run b0
  where
  b0 : Chain (Sw23 ∷ CX21 ∷ Sw23 ∷ []) (CX31 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 0 3 (CX31 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 CK21: 3 steps
lem-sw2-CK21 : ⟪ (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK31 ∷ []) ⟫ʷ
lem-sw2-CK21 = run b0
  where
  b0 : Chain (Sw23 ∷ CK21 ∷ Sw23 ∷ []) (CK31 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 0 3 (CK31 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 CKd21: 3 steps
lem-sw2-CKd21 : ⟪ (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK31⁻ ∷ []) ⟫ʷ
lem-sw2-CKd21 = run b0
  where
  b0 : Chain (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) (CK31⁻ ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 0 3 (CK31⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 CS23: 2 steps
lem-sw2-CS23 : ⟪ (Sw23 ∷ CS23 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ []) ⟫ʷ
lem-sw2-CS23 = run b0
  where
  b0 : Chain (Sw23 ∷ CS23 ∷ Sw23 ∷ []) (CS23 ∷ [])
  b0 = at 0 2 (CS23 ∷ Sw23 ∷ []) wn00071 ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 CSd23: 2 steps
lem-sw2-CSd23 : ⟪ (Sw23 ∷ CS23⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ []) ⟫ʷ
lem-sw2-CSd23 = run b0
  where
  b0 : Chain (Sw23 ∷ CS23⁻ ∷ Sw23 ∷ []) (CS23⁻ ∷ [])
  b0 = at 0 2 (CS23⁻ ∷ Sw23 ∷ []) wn00072 ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 CZ23: 2 steps
lem-sw2-CZ23 : ⟪ (Sw23 ∷ CZ23 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CZ23 ∷ []) ⟫ʷ
lem-sw2-CZ23 = run b0
  where
  b0 : Chain (Sw23 ∷ CZ23 ∷ Sw23 ∷ []) (CZ23 ∷ [])
  b0 = at 0 2 (CZ23 ∷ Sw23 ∷ []) wn00377 ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 CX23: 2 steps
lem-sw2-CX23 : ⟪ (Sw23 ∷ CX23 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CX32 ∷ []) ⟫ʷ
lem-sw2-CX23 = run b0
  where
  b0 : Chain (Sw23 ∷ CX23 ∷ Sw23 ∷ []) (CX32 ∷ [])
  b0 = at 0 2 (CX32 ∷ Sw23 ∷ []) wn00378 ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 CK23: 2 steps
lem-sw2-CK23 : ⟪ (Sw23 ∷ CK23 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK32 ∷ []) ⟫ʷ
lem-sw2-CK23 = run b0
  where
  b0 : Chain (Sw23 ∷ CK23 ∷ Sw23 ∷ []) (CK32 ∷ [])
  b0 = at 0 2 (CK32 ∷ Sw23 ∷ []) wn00379 ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 CKd23: 2 steps
lem-sw2-CKd23 : ⟪ (Sw23 ∷ CK23⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK32⁻ ∷ []) ⟫ʷ
lem-sw2-CKd23 = run b0
  where
  b0 : Chain (Sw23 ∷ CK23⁻ ∷ Sw23 ∷ []) (CK32⁻ ∷ [])
  b0 = at 0 2 (CK32⁻ ∷ Sw23 ∷ []) wn00380 ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 CX30: 3 steps
lem-sw2-CX30 : ⟪ (Sw23 ∷ CX30 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CX20 ∷ []) ⟫ʷ
lem-sw2-CX30 = run b0
  where
  b0 : Chain (Sw23 ∷ CX30 ∷ Sw23 ∷ []) (CX20 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] wn00003 ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 CK30: 3 steps
lem-sw2-CK30 : ⟪ (Sw23 ∷ CK30 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK20 ∷ []) ⟫ʷ
lem-sw2-CK30 = run b0
  where
  b0 : Chain (Sw23 ∷ CK30 ∷ Sw23 ∷ []) (CK20 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] wn00003 ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 CKd30: 3 steps
lem-sw2-CKd30 : ⟪ (Sw23 ∷ CK30⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK20⁻ ∷ []) ⟫ʷ
lem-sw2-CKd30 = run b0
  where
  b0 : Chain (Sw23 ∷ CK30⁻ ∷ Sw23 ∷ []) (CK20⁻ ∷ [])
  b0 = at 1 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] wn00003 ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 CX31: 3 steps
lem-sw2-CX31 : ⟪ (Sw23 ∷ CX31 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CX21 ∷ []) ⟫ʷ
lem-sw2-CX31 = run b0
  where
  b0 : Chain (Sw23 ∷ CX31 ∷ Sw23 ∷ []) (CX21 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] wn00003 ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 CK31: 3 steps
lem-sw2-CK31 : ⟪ (Sw23 ∷ CK31 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK21 ∷ []) ⟫ʷ
lem-sw2-CK31 = run b0
  where
  b0 : Chain (Sw23 ∷ CK31 ∷ Sw23 ∷ []) (CK21 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] wn00003 ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 CKd31: 3 steps
lem-sw2-CKd31 : ⟪ (Sw23 ∷ CK31⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK21⁻ ∷ []) ⟫ʷ
lem-sw2-CKd31 = run b0
  where
  b0 : Chain (Sw23 ∷ CK31⁻ ∷ Sw23 ∷ []) (CK21⁻ ∷ [])
  b0 = at 1 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] wn00003 ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 CX32: 2 steps
lem-sw2-CX32 : ⟪ (Sw23 ∷ CX32 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ []) ⟫ʷ
lem-sw2-CX32 = run b0
  where
  b0 : Chain (Sw23 ∷ CX32 ∷ Sw23 ∷ []) (CX23 ∷ [])
  b0 = at 0 2 (CX23 ∷ Sw23 ∷ []) wn00381 ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 CK32: 2 steps
lem-sw2-CK32 : ⟪ (Sw23 ∷ CK32 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK23 ∷ []) ⟫ʷ
lem-sw2-CK32 = run b0
  where
  b0 : Chain (Sw23 ∷ CK32 ∷ Sw23 ∷ []) (CK23 ∷ [])
  b0 = at 0 2 (CK23 ∷ Sw23 ∷ []) wn00382 ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 CKd32: 2 steps
lem-sw2-CKd32 : ⟪ (Sw23 ∷ CK32⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK23⁻ ∷ []) ⟫ʷ
lem-sw2-CKd32 = run b0
  where
  b0 : Chain (Sw23 ∷ CK32⁻ ∷ Sw23 ∷ []) (CK23⁻ ∷ [])
  b0 = at 0 2 (CK23⁻ ∷ Sw23 ∷ []) wn00383 ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 CCZ012: 22 steps
lem-sw2-CCZ012 : ⟪ (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ []) ⟫ʷ
lem-sw2-CCZ012 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 0 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b1 : Chain (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ []) (Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ [])
  b1 = at 4 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00003 ▸
       at 2 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b2 : Chain (Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ []) (CCZ013 ∷ [])
  b2 = at 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 1 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00043 ▸
       at 1 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 CCZ013: 22 steps
lem-sw2-CCZ013 : ⟪ (Sw23 ∷ CCZ013 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ []) ⟫ʷ
lem-sw2-CCZ013 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw23 ∷ CCZ013 ∷ Sw23 ∷ []) (Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b1 : Chain (Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ Sw23 ∷ [])
  b1 = at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸
       at 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] wn00003 ▸
       at 1 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸ done

  b2 : Chain (CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ Sw23 ∷ []) (CCZ012 ∷ [])
  b2 = at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸
       at 0 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00043 ▸
       at 0 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 CCZ023: 38 steps
lem-sw2-CCZ023 : ⟪ (Sw23 ∷ CCZ023 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ []) ⟫ʷ
lem-sw2-CCZ023 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (run b4))))
  where
  b0 : Chain (Sw23 ∷ CCZ023 ∷ Sw23 ∷ []) (Sw23 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 2 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 3 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 4 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b1 : Chain (Sw23 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Sw23 ∷ []) (CS23 ∷ CX03 ∷ CS23⁻ ∷ Sw23 ∷ CX02 ∷ CS03 ∷ Sw23 ∷ [])
  b1 = at 6 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00031 ▸
       at 0 2 (CS23 ∷ Sw23 ∷ []) wn00071 ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CS23⁻ ∷ Sw23 ∷ []) wn00072 ▸ done

  b2 : Chain (CS23 ∷ CX03 ∷ CS23⁻ ∷ Sw23 ∷ CX02 ∷ CS03 ∷ Sw23 ∷ []) (Sw01 ∷ CS23 ∷ Sw23 ∷ Sw01 ∷ CX02 ∷ Sw23 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ [])
  b2 = at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸
       at 0 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 1 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 3 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b3 : Chain (Sw01 ∷ CS23 ∷ Sw23 ∷ Sw01 ∷ CX02 ∷ Sw23 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ []) (Sw01 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ Sw01 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ [])
  b3 = at 3 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 4 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 2 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 5 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b4 : Chain (Sw01 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ Sw01 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ []) (CCZ023 ∷ [])
  b4 = at 4 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 1 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00073 ▸
       at 1 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 CCZ123: 12 steps
lem-sw2-CCZ123 : ⟪ (Sw23 ∷ CCZ123 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ []) ⟫ʷ
lem-sw2-CCZ123 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw23 ∷ CCZ123 ∷ Sw23 ∷ []) (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (CS23 ∷ Sw23 ∷ []) wn00071 ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CS23⁻ ∷ Sw23 ∷ []) wn00072 ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ []) (CCZ123 ∷ [])
  b1 = at 4 2 [] wn00003 ▸
       at 0 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00073 ▸
       at 0 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 TOFF012: 28 steps
lem-sw2-TOFF012 : ⟪ (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ []) ⟫ʷ
lem-sw2-TOFF012 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ [])
  b0 = at 1 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b1 : Chain (K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ [])
  b1 = at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 7 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸ done

  b2 : Chain (Sw23 ∷ K0 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ [])
  b2 = at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸
       at 7 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸ done

  b3 : Chain (Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ []) (Toff013 ∷ [])
  b3 = at 1 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) wn00056 ▸
       at 1 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 TOFF013: 28 steps
lem-sw2-TOFF013 : ⟪ (Sw23 ∷ Toff013 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ []) ⟫ʷ
lem-sw2-TOFF013 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Sw23 ∷ Toff013 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ []) (K0 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ [])
  b1 = at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 9 2 [] wn00003 ▸
       at 0 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (K0 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ Sw23 ∷ ι ∷ Sw23 ∷ [])
  b2 = at 1 2 [] wn00003 ▸
       at 2 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 6 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸ done

  b3 : Chain (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ Sw23 ∷ ι ∷ Sw23 ∷ []) (Toff012 ∷ [])
  b3 = at 7 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 0 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) wn00056 ▸
       at 0 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 TOFF023: 47 steps
lem-sw2-TOFF023 : ⟪ (Sw23 ∷ Toff023 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ []) ⟫ʷ
lem-sw2-TOFF023 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (run b5)))))
  where
  b0 : Chain (Sw23 ∷ Toff023 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 2 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 3 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 4 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 5 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw23 ∷ []) (K0 ∷ Sw23 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ [])
  b1 = at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 8 2 (ι ∷ Sw01 ∷ []) wn00122 ▸
       at 9 2 [] wn00031 ▸
       at 0 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸ done

  b2 : Chain (K0 ∷ Sw23 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ []) (K0 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw23 ∷ [])
  b2 = at 1 2 (CS23 ∷ Sw23 ∷ []) wn00071 ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS23⁻ ∷ Sw23 ∷ []) wn00072 ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸ done

  b3 : Chain (K0 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw23 ∷ []) (Sw01 ∷ K1 ∷ CS23 ∷ Sw23 ∷ CX12 ∷ Sw01 ∷ Sw23 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ [])
  b3 = at 6 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 7 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 0 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 1 2 (K1 ∷ Sw01 ∷ []) wn00123 ▸
       at 2 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 4 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 4 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸ done

  b4 : Chain (Sw01 ∷ K1 ∷ CS23 ∷ Sw23 ∷ CX12 ∷ Sw01 ∷ Sw23 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ []) (Sw01 ∷ K1 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ Sw01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ [])
  b4 = at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 3 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 6 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸ done

  b5 : Chain (Sw01 ∷ K1 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ Sw01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ []) (Toff023 ∷ [])
  b5 = at 6 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 7 2 (K1 ∷ Sw01 ∷ []) wn00123 ▸
       at 8 2 (ι1 ∷ Sw01 ∷ []) wn00124 ▸
       at 1 8 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) wn00384 ▸
       at 1 8 (Toff123 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff023 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 TOFF102: 28 steps
lem-sw2-TOFF102 : ⟪ (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ []) ⟫ʷ
lem-sw2-TOFF102 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) (K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ [])
  b0 = at 1 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b1 : Chain (K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ []) (Sw23 ∷ K1 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw23 ∷ [])
  b1 = at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 7 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸ done

  b2 : Chain (Sw23 ∷ K1 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw23 ∷ []) (Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ [])
  b2 = at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸
       at 7 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸ done

  b3 : Chain (Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ []) (Toff103 ∷ [])
  b3 = at 1 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) wn00196 ▸
       at 1 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff103 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 TOFF103: 28 steps
lem-sw2-TOFF103 : ⟪ (Sw23 ∷ Toff103 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ []) ⟫ʷ
lem-sw2-TOFF103 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Sw23 ∷ Toff103 ∷ Sw23 ∷ []) (Sw23 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw23 ∷ []) (K1 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw23 ∷ [])
  b1 = at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 9 2 [] wn00003 ▸
       at 0 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (K1 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw23 ∷ []) (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ Sw23 ∷ ι ∷ Sw23 ∷ [])
  b2 = at 1 2 [] wn00003 ▸
       at 2 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 6 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸ done

  b3 : Chain (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ Sw23 ∷ ι ∷ Sw23 ∷ []) (Toff102 ∷ [])
  b3 = at 7 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 0 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) wn00196 ▸
       at 0 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 TOFF123: 15 steps
lem-sw2-TOFF123 : ⟪ (Sw23 ∷ Toff123 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Toff123 ∷ []) ⟫ʷ
lem-sw2-TOFF123 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw23 ∷ Toff123 ∷ Sw23 ∷ []) (K1 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ Sw23 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 1 2 (CS23 ∷ Sw23 ∷ []) wn00071 ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS23⁻ ∷ Sw23 ∷ []) wn00072 ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (K1 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ Sw23 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw23 ∷ []) (Toff123 ∷ [])
  b1 = at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 6 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 7 2 (ι1 ∷ Sw23 ∷ []) (sym (low-comm ((iI ↑)) (Swap))) ▸
       at 0 8 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) wn00384 ▸
       at 0 8 (Toff123 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 TOFF201: 28 steps
lem-sw2-TOFF201 : ⟪ (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ []) ⟫ʷ
lem-sw2-TOFF201 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) (K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ [])
  b0 = at 1 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (K3 ∷ Sw23 ∷ []) wn00335 ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b1 : Chain (K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ []) (Sw23 ∷ K2 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw23 ∷ Sw23 ∷ [])
  b1 = at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K3 ∷ Sw23 ∷ []) wn00335 ▸
       at 7 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 2 (K2 ∷ Sw23 ∷ []) wn00336 ▸
       at 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸ done

  b2 : Chain (Sw23 ∷ K2 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw23 ∷ Sw23 ∷ []) (Sw23 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ [])
  b2 = at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸
       at 7 2 (K2 ∷ Sw23 ∷ []) wn00336 ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸ done

  b3 : Chain (Sw23 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ []) (Toff301 ∷ [])
  b3 = at 1 8 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) wn00368 ▸
       at 1 8 (Toff201 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff301 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00003 ▸ done

-- sw2 TOFF203: 47 steps
lem-sw2-TOFF203 : ⟪ (Sw23 ∷ Toff203 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ []) ⟫ʷ
lem-sw2-TOFF203 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (run b5)))))
  where
  b0 : Chain (Sw23 ∷ Toff203 ∷ Sw23 ∷ []) (Sw23 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ K2 ∷ ι1 ∷ Sw01 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw01 ∷ Toff213 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 2 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 3 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 4 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 5 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ K2 ∷ ι1 ∷ Sw01 ∷ Sw23 ∷ []) (K3 ∷ Sw23 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ Sw23 ∷ [])
  b1 = at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 8 2 (ι ∷ Sw01 ∷ []) wn00122 ▸
       at 9 2 [] wn00031 ▸
       at 0 2 (K3 ∷ Sw23 ∷ []) wn00335 ▸ done

  b2 : Chain (K3 ∷ Sw23 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ Sw23 ∷ []) (K3 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ Sw23 ∷ K2 ∷ ι ∷ Sw23 ∷ [])
  b2 = at 1 2 (CS23 ∷ Sw23 ∷ []) wn00071 ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS23⁻ ∷ Sw23 ∷ []) wn00072 ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸ done

  b3 : Chain (K3 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ Sw23 ∷ K2 ∷ ι ∷ Sw23 ∷ []) (Sw01 ∷ K3 ∷ CS23 ∷ Sw23 ∷ CX12 ∷ Sw01 ∷ Sw23 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ K3 ∷ ι ∷ Sw23 ∷ Sw23 ∷ [])
  b3 = at 6 2 (K3 ∷ Sw23 ∷ []) wn00335 ▸
       at 7 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 0 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 1 2 (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑))) ▸
       at 2 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 4 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 4 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸ done

  b4 : Chain (Sw01 ∷ K3 ∷ CS23 ∷ Sw23 ∷ CX12 ∷ Sw01 ∷ Sw23 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ K3 ∷ ι ∷ Sw23 ∷ Sw23 ∷ []) (Sw01 ∷ K3 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ Sw01 ∷ CS02 ∷ K3 ∷ ι ∷ Sw23 ∷ Sw23 ∷ [])
  b4 = at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 3 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 6 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸ done

  b5 : Chain (Sw01 ∷ K3 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ Sw01 ∷ CS02 ∷ K3 ∷ ι ∷ Sw23 ∷ Sw23 ∷ []) (Toff302 ∷ [])
  b5 = at 6 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 7 2 (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑))) ▸
       at 8 2 (ι1 ∷ Sw01 ∷ []) wn00124 ▸
       at 1 8 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) wn00385 ▸
       at 1 8 (Toff312 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff302 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00003 ▸ done

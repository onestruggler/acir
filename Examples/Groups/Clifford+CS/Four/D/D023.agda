{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D023 where

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
open import Examples.Groups.Clifford+CS.Four.Wins.W01 using (wn00001 ; wn00003 ; wn00005 ; wn00006 ; wn00007 ; wn00020 ; wn00024 ; wn00025 ; wn00026 ; wn00027 ; wn00029 ; wn00030 ; wn00031 ; wn00039 ; wn00049 ; wn00056 ; wn00067 ; wn00074 ; wn00075 ; wn00076 ; wn00081 ; wn00091 ; wn00100 ; wn00104 ; wn00118 ; wn00121 ; wn00122 ; wn00123 ; wn00124 ; wn00125 ; wn00127 ; wn00137 ; wn00139 ; wn00140 ; wn00142 ; wn00173 ; wn00175)
open import Examples.Groups.Clifford+CS.Four.Wins.W02 using (wn00316 ; wn00334 ; wn00391 ; wn00392 ; wn00393 ; wn00394)
open import Examples.Groups.Clifford+CS.Four.Wins.W03 using (wn00416 ; wn00419 ; wn00420 ; wn00421 ; wn00422 ; wn00423 ; wn00424 ; wn00425 ; wn00426 ; wn00427 ; wn00428 ; wn00429 ; wn00430 ; wn00431 ; wn00432 ; wn00433 ; wn00434 ; wn00435 ; wn00436 ; wn00437 ; wn00438 ; wn00439 ; wn00440 ; wn00441 ; wn00442 ; wn00443 ; wn00444 ; wn00445 ; wn00446 ; wn00447 ; wn00448 ; wn00449 ; wn00450 ; wn00451 ; wn00452 ; wn00453 ; wn00454 ; wn00455 ; wn00456 ; wn00457)
open import Examples.Groups.Clifford+CS.Canonical using (can-≈)

-- pass [X3 CK32 X3] [TOFF023]: 67 steps
lem-pass-X3-CK32-X3-vs-TOFF023 : ⟪ (X3 ∷ CK32 ∷ X3 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ X3 ∷ CK32 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CK32-X3-vs-TOFF023 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (run b8))))))))
  where
  b0 : Chain (X3 ∷ CK32 ∷ X3 ∷ Toff023 ∷ []) (X3 ∷ CK32 ∷ X3 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ [])
  b0 = at 4 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 3 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 4 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 5 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 6 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 7 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸ done

  b1 : Chain (X3 ∷ CK32 ∷ X3 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ []) (X3 ∷ CK32 ∷ X3 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ Sw01 ∷ Sw01 ∷ [])
  b1 = at 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 10 2 (ι ∷ Sw01 ∷ []) wn00122 ▸
       at 11 2 [] wn00031 ▸ done

  b2 : Chain (X3 ∷ CK32 ∷ X3 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ Sw01 ∷ Sw01 ∷ []) (X3 ∷ CK32 ∷ X3 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ [])
  b2 = at 10 2 (Sw01 ∷ ι1 ∷ []) wn00127 ▸
       at 9 2 (Sw01 ∷ K1 ∷ []) wn00118 ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 9 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 8 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 9 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸ done

  b3 : Chain (X3 ∷ CK32 ∷ X3 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ []) (X3 ∷ Sw01 ∷ CK32 ∷ X3 ∷ Toff123 ∷ Sw01 ∷ [])
  b3 = at 6 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 5 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸
       at 4 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 3 2 (Sw01 ∷ K1 ∷ []) wn00118 ▸
       at 4 8 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) wn00125 ▸
       at 4 8 (Toff123 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸
       at 1 2 (Sw01 ∷ CK32 ∷ []) (sym (low-comm (Swap) (CK₁₀))) ▸ done

  b4 : Chain (X3 ∷ Sw01 ∷ CK32 ∷ X3 ∷ Toff123 ∷ Sw01 ∷ []) (K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ K1 ∷ ι1 ∷ X3 ∷ CK32 ∷ X3 ∷ Sw01 ∷ [])
  b4 = at 0 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸
       at 1 4 (Toff123 ∷ X3 ∷ CK32 ∷ X3 ∷ []) wn00419 ▸
       at 1 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 1 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 2 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 3 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 4 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸ done

  b5 : Chain (K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ K1 ∷ ι1 ∷ X3 ∷ CK32 ∷ X3 ∷ Sw01 ∷ []) (Sw01 ∷ Sw01 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ Sw01 ∷ X3 ∷ CK32 ∷ X3 ∷ Sw01 ∷ [])
  b5 = at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 7 2 (ι ∷ Sw01 ∷ []) wn00122 ▸
       at 0 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸ done

  b6 : Chain (Sw01 ∷ Sw01 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ Sw01 ∷ X3 ∷ CK32 ∷ X3 ∷ Sw01 ∷ []) (Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ CS12 ∷ Sw01 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw01 ∷ X3 ∷ CK32 ∷ X3 ∷ Sw01 ∷ [])
  b6 = at 1 2 (K1 ∷ Sw01 ∷ []) wn00123 ▸
       at 2 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 3 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 4 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 5 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸ done

  b7 : Chain (Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ CS12 ∷ Sw01 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw01 ∷ X3 ∷ CK32 ∷ X3 ∷ Sw01 ∷ []) (Toff023 ∷ X3 ∷ Sw01 ∷ CK32 ∷ X3 ∷ Sw01 ∷ [])
  b7 = at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K1 ∷ Sw01 ∷ []) wn00123 ▸
       at 8 2 (ι1 ∷ Sw01 ∷ []) wn00124 ▸
       at 1 8 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) wn00125 ▸
       at 1 8 (Toff123 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff023 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸ done

  b8 : Chain (Toff023 ∷ X3 ∷ Sw01 ∷ CK32 ∷ X3 ∷ Sw01 ∷ []) (Toff023 ∷ X3 ∷ CK32 ∷ X3 ∷ [])
  b8 = at 2 2 (CK32 ∷ Sw01 ∷ []) (low-comm (Swap) (CK₁₀)) ▸
       at 3 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸
       at 4 2 [] wn00031 ▸ done

-- pass [X3 CK32 X3] [CS01]: 3 steps
lem-pass-X3-CK32-X3-vs-CS01 : ⟪ (X3 ∷ CK32 ∷ X3 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ X3 ∷ CK32 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CK32-X3-vs-CS01 = run b0
  where
  b0 : Chain (X3 ∷ CK32 ∷ X3 ∷ CS01 ∷ []) (CS01 ∷ X3 ∷ CK32 ∷ X3 ∷ [])
  b0 = at 2 2 (CS01 ∷ X3 ∷ []) (sym (low-comm (CS) ((X ↑)))) ▸
       at 1 2 (CS01 ∷ CK32 ∷ []) (sym (low-comm (CS) (CK₁₀))) ▸
       at 0 2 (CS01 ∷ X3 ∷ []) (sym (low-comm (CS) ((X ↑)))) ▸ done

-- pass [X3 CK32 X3] [CSd01]: 3 steps
lem-pass-X3-CK32-X3-vs-CSd01 : ⟪ (X3 ∷ CK32 ∷ X3 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ X3 ∷ CK32 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CK32-X3-vs-CSd01 = run b0
  where
  b0 : Chain (X3 ∷ CK32 ∷ X3 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ X3 ∷ CK32 ∷ X3 ∷ [])
  b0 = at 2 2 (CS01⁻ ∷ X3 ∷ []) (sym (low-comm ((CS • CS • CS)) ((X ↑)))) ▸
       at 1 2 (CS01⁻ ∷ CK32 ∷ []) (sym (low-comm ((CS • CS • CS)) (CK₁₀))) ▸
       at 0 2 (CS01⁻ ∷ X3 ∷ []) (sym (low-comm ((CS • CS • CS)) ((X ↑)))) ▸ done

-- pass [CS13] [iI]: 3 steps
lem-pass-CS13-vs-iI : ⟪ (CS13 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ CS13 ∷ []) ⟫ʷ
lem-pass-CS13-vs-iI = run b0
  where
  b0 : Chain (CS13 ∷ ι ∷ []) (ι ∷ CS13 ∷ [])
  b0 = at 1 1 (ι3 ∷ []) (trans (can-≈ (iI)) (sym (can-≈ ((iI ↑ ↑ ↑))))) ▸
       at 0 2 (ι3 ∷ CS13 ∷ []) wn00420 ▸
       at 0 1 (ι ∷ []) (trans (can-≈ ((iI ↑ ↑ ↑))) (sym (can-≈ (iI)))) ▸ done

-- pass [CS13] [Sd3]: 1 steps
lem-pass-CS13-vs-Sd3 : ⟪ (CS13 ∷ S3⁻ ∷ []) ⟫ʷ ≈ ⟪ (S3⁻ ∷ CS13 ∷ []) ⟫ʷ
lem-pass-CS13-vs-Sd3 = run b0
  where
  b0 : Chain (CS13 ∷ S3⁻ ∷ []) (S3⁻ ∷ CS13 ∷ [])
  b0 = at 0 2 (S3⁻ ∷ CS13 ∷ []) wn00421 ▸ done

-- pass [CS13] [S3]: 1 steps
lem-pass-CS13-vs-S3 : ⟪ (CS13 ∷ S3 ∷ []) ⟫ʷ ≈ ⟪ (S3 ∷ CS13 ∷ []) ⟫ʷ
lem-pass-CS13-vs-S3 = run b0
  where
  b0 : Chain (CS13 ∷ S3 ∷ []) (S3 ∷ CS13 ∷ [])
  b0 = at 0 2 (S3 ∷ CS13 ∷ []) wn00422 ▸ done

-- pass [CS13] [X3 TOFF013 X3]: 65 steps
lem-pass-CS13-vs-X3-TOFF013-X3 : ⟪ (CS13 ∷ X3 ∷ Toff013 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff013 ∷ X3 ∷ CS13 ∷ []) ⟫ʷ
lem-pass-CS13-vs-X3-TOFF013-X3 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (run b8))))))))
  where
  b0 : Chain (CS13 ∷ X3 ∷ Toff013 ∷ X3 ∷ []) (CS13 ∷ X3 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ [])
  b0 = at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 2 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b1 : Chain (CS13 ∷ X3 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ []) (CS13 ∷ X3 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ X2 ∷ Sw23 ∷ [])
  b1 = at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 10 2 [] wn00003 ▸ done

  b2 : Chain (CS13 ∷ X3 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ X2 ∷ Sw23 ∷ []) (CS13 ∷ X3 ∷ K0 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ X2 ∷ Sw23 ∷ [])
  b2 = at 9 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 8 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00003 ▸
       at 6 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00003 ▸
       at 4 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸ done

  b3 : Chain (CS13 ∷ X3 ∷ K0 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ X2 ∷ Sw23 ∷ []) (Sw23 ∷ CS12 ∷ X2 ∷ Toff012 ∷ X2 ∷ Sw23 ∷ [])
  b3 = at 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 2 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 3 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) wn00056 ▸
       at 3 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 0 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸ done

  b4 : Chain (Sw23 ∷ CS12 ∷ X2 ∷ Toff012 ∷ X2 ∷ Sw23 ∷ []) (X3 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ X2 ∷ CS12 ∷ Sw23 ∷ [])
  b4 = at 1 4 (X2 ∷ Toff012 ∷ X2 ∷ CS12 ∷ []) wn00423 ▸
       at 0 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 2 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b5 : Chain (X3 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ X2 ∷ CS12 ∷ Sw23 ∷ []) (X3 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ X2 ∷ CS12 ∷ Sw23 ∷ [])
  b5 = at 4 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸ done

  b6 : Chain (X3 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ X2 ∷ CS12 ∷ Sw23 ∷ []) (X3 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw23 ∷ X2 ∷ CS12 ∷ Sw23 ∷ [])
  b6 = at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00003 ▸ done

  b7 : Chain (X3 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw23 ∷ X2 ∷ CS12 ∷ Sw23 ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ CS13 ∷ Sw23 ∷ Sw23 ∷ [])
  b7 = at 8 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 2 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) wn00056 ▸
       at 2 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b8 : Chain (X3 ∷ Toff013 ∷ X3 ∷ CS13 ∷ Sw23 ∷ Sw23 ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ CS13 ∷ [])
  b8 = at 4 2 [] wn00003 ▸ done

-- comm CCZ023 CS13: 131 steps
lem-comm-CCZ023-CS13 : ⟪ (CCZ023 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CCZ023 ∷ []) ⟫ʷ
lem-comm-CCZ023-CS13 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (run b16))))))))))))))))
  where
  b0 : Chain (CCZ023 ∷ CS13 ∷ []) (CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CS13 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 0 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 1 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 2 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 3 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CS13 ∷ []) (CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ CS13 ∷ [])
  b1 = at 4 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 4 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00031 ▸
       at 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 5 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸ done

  b2 : Chain (CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ CS13 ∷ []) (Sw01 ∷ CCZ123 ∷ Sw01 ∷ CS13 ∷ [])
  b2 = at 4 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸
       at 2 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 1 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸
       at 0 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 1 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸
       at 1 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (Sw01 ∷ CCZ123 ∷ Sw01 ∷ CS13 ∷ []) (CS02 ∷ CX30 ∷ CS02⁻ ∷ Sw01 ∷ CX31 ∷ CS23 ∷ Sw01 ∷ CS13 ∷ [])
  b3 = at 1 1 (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) wn00075 ▸
       at 0 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 2 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 2 2 (CX20 ∷ Sw01 ∷ []) wn00039 ▸
       at 3 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸ done

  b4 : Chain (CS02 ∷ CX30 ∷ CS02⁻ ∷ Sw01 ∷ CX31 ∷ CS23 ∷ Sw01 ∷ CS13 ∷ []) (CS02 ∷ CX30 ∷ CS02⁻ ∷ CX30 ∷ CS13 ∷ CS23 ∷ [])
  b4 = at 4 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 4 2 (CX20 ∷ Sw01 ∷ []) wn00039 ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 3 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 5 2 [] wn00031 ▸
       at 4 2 (CS13 ∷ CS23 ∷ []) wn00091 ▸ done

  b5 : Chain (CS02 ∷ CX30 ∷ CS02⁻ ∷ CX30 ∷ CS13 ∷ CS23 ∷ []) (CS02 ∷ CX30 ∷ CS02⁻ ∷ CS13 ∷ Sw23 ∷ CX20 ∷ Sw23 ∷ CS23 ∷ [])
  b5 = at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸
       at 3 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 4 2 (CS12 ∷ CX20 ∷ []) wn00424 ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b6 : Chain (CS02 ∷ CX30 ∷ CS02⁻ ∷ CS13 ∷ Sw23 ∷ CX20 ∷ Sw23 ∷ CS23 ∷ []) (CS02 ∷ CX30 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CX30 ∷ CS23 ∷ [])
  b6 = at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b7 : Chain (CS02 ∷ CX30 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CX30 ∷ CS23 ∷ []) (CS02 ∷ CX30 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Sw23 ∷ CX30 ∷ CS23 ∷ [])
  b7 = at 7 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS23 ∷ Sw12 ∷ []) wn00020 ▸
       at 5 2 (CS23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (CS)) ▸
       at 4 2 (CS13 ∷ Sw12 ∷ []) wn00049 ▸
       at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸
       at 4 5 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b8 : Chain (CS02 ∷ CX30 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Sw23 ∷ CX30 ∷ CS23 ∷ []) (CS02 ∷ Sw23 ∷ CS12 ∷ CX20 ∷ Sw23 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ [])
  b8 = at 6 2 [] wn00003 ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸
       at 1 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸
       at 2 2 (CS12 ∷ CX20 ∷ []) wn00424 ▸ done

  b9 : Chain (CS02 ∷ Sw23 ∷ CS12 ∷ CX20 ∷ Sw23 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ []) (Sw23 ∷ CS03 ∷ CS12 ∷ Sw23 ∷ CX30 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ [])
  b9 = at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸
       at 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b10 : Chain (Sw23 ∷ CS03 ∷ CS12 ∷ Sw23 ∷ CX30 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ []) (Sw23 ∷ CS12 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CX30 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ [])
  b10 = at 1 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS23 ∷ Sw12 ∷ []) wn00020 ▸
       at 3 2 (CS23 ∷ CS01 ∷ []) (low-comm (CS) (CS)) ▸
       at 2 2 (CS13 ∷ Sw12 ∷ []) wn00049 ▸
       at 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00003 ▸ done

  b11 : Chain (Sw23 ∷ CS12 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CX30 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ []) (CS13 ∷ CS02 ∷ CX30 ∷ CS02⁻ ∷ Sw23 ∷ CX20 ∷ Sw01 ∷ Sw23 ∷ CS23 ∷ Sw01 ∷ [])
  b11 = at 2 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸
       at 0 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 5 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 4 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b12 : Chain (CS13 ∷ CS02 ∷ CX30 ∷ CS02⁻ ∷ Sw23 ∷ CX20 ∷ Sw01 ∷ Sw23 ∷ CS23 ∷ Sw01 ∷ []) (CS13 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ Sw01 ∷ [])
  b12 = at 5 2 (Sw01 ∷ CX21 ∷ []) wn00006 ▸
       at 4 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 5 3 (CX31 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw01 ∷ CS12⁻ ∷ []) wn00076 ▸
       at 2 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 3 2 (Sw01 ∷ CX21 ∷ []) wn00006 ▸
       at 2 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b13 : Chain (CS13 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ Sw01 ∷ []) (CS13 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ Sw01 ∷ [])
  b13 = at 3 3 (CX31 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 2 5 (CCZ123 ∷ []) wn00081 ▸
       at 2 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 2 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 3 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 4 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸ done

  b14 : Chain (CS13 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ Sw01 ∷ []) (CS13 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ Sw01 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ Sw01 ∷ [])
  b14 = at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 2 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 3 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸ done

  b15 : Chain (CS13 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ Sw01 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ Sw01 ∷ []) (CS13 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ [])
  b15 = at 4 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 5 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸ done

  b16 : Chain (CS13 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ []) (CS13 ∷ CCZ023 ∷ [])
  b16 = at 2 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00031 ▸ done

-- pass [CS13] [CSd01]: 9 steps
lem-pass-CS13-vs-CSd01 : ⟪ (CS13 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ CS13 ∷ []) ⟫ʷ
lem-pass-CS13-vs-CSd01 = trans (run b0) (run b1)
  where
  b0 : Chain (CS13 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CS13 ∷ Sw23 ∷ Sw23 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 2 (Sw23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (Swap)) ▸
       at 0 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸
       at 1 2 (CS01⁻ ∷ CS12 ∷ []) wn00425 ▸
       at 0 2 (CS01⁻ ∷ Sw23 ∷ []) (sym (low-comm ((CS • CS • CS)) (Swap))) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (CS01⁻ ∷ CS13 ∷ Sw23 ∷ Sw23 ∷ []) (CS01⁻ ∷ CS13 ∷ [])
  b1 = at 2 2 [] wn00003 ▸ done

-- pass [CS13] [CS01]: 9 steps
lem-pass-CS13-vs-CS01 : ⟪ (CS13 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CS13 ∷ []) ⟫ʷ
lem-pass-CS13-vs-CS01 = trans (run b0) (run b1)
  where
  b0 : Chain (CS13 ∷ CS01 ∷ []) (CS01 ∷ CS13 ∷ Sw23 ∷ Sw23 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 2 (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap)) ▸
       at 0 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸
       at 1 2 (CS01 ∷ CS12 ∷ []) wn00067 ▸
       at 0 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (CS01 ∷ CS13 ∷ Sw23 ∷ Sw23 ∷ []) (CS01 ∷ CS13 ∷ [])
  b1 = at 2 2 [] wn00003 ▸ done

-- b2g 1011R2: 4 steps
lem-b2g-1011R2 : ⟪ (X0 ∷ X2 ∷ X3 ∷ S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X0 ∷ X3 ∷ []) ⟫ʷ
lem-b2g-1011R2 = run b0
  where
  b0 : Chain (X0 ∷ X2 ∷ X3 ∷ S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X0 ∷ X3 ∷ [])
  b0 = at 1 2 (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X)) ▸
       at 11 2 (X2 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑))) ▸
       at 2 3 (S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ []) wn00393 ▸
       at 10 3 (S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ []) wn00394 ▸ done

-- pass [CS23] [iI]: 3 steps
lem-pass-CS23-vs-iI : ⟪ (CS23 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ CS23 ∷ []) ⟫ʷ
lem-pass-CS23-vs-iI = run b0
  where
  b0 : Chain (CS23 ∷ ι ∷ []) (ι ∷ CS23 ∷ [])
  b0 = at 1 1 (ι3 ∷ []) (trans (can-≈ (iI)) (sym (can-≈ ((iI ↑ ↑ ↑))))) ▸
       at 0 2 (ι3 ∷ CS23 ∷ []) wn00426 ▸
       at 0 1 (ι ∷ []) (trans (can-≈ ((iI ↑ ↑ ↑))) (sym (can-≈ (iI)))) ▸ done

-- pass [CS23] [Sd3]: 1 steps
lem-pass-CS23-vs-Sd3 : ⟪ (CS23 ∷ S3⁻ ∷ []) ⟫ʷ ≈ ⟪ (S3⁻ ∷ CS23 ∷ []) ⟫ʷ
lem-pass-CS23-vs-Sd3 = run b0
  where
  b0 : Chain (CS23 ∷ S3⁻ ∷ []) (S3⁻ ∷ CS23 ∷ [])
  b0 = at 0 2 (S3⁻ ∷ CS23 ∷ []) wn00427 ▸ done

-- pass [CS23] [S3]: 1 steps
lem-pass-CS23-vs-S3 : ⟪ (CS23 ∷ S3 ∷ []) ⟫ʷ ≈ ⟪ (S3 ∷ CS23 ∷ []) ⟫ʷ
lem-pass-CS23-vs-S3 = run b0
  where
  b0 : Chain (CS23 ∷ S3 ∷ []) (S3 ∷ CS23 ∷ [])
  b0 = at 0 2 (S3 ∷ CS23 ∷ []) wn00428 ▸ done

-- pass [TOFF201] [iI]: 1 steps
lem-pass-TOFF201-vs-iI : ⟪ (Toff201 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ Toff201 ∷ []) ⟫ʷ
lem-pass-TOFF201-vs-iI = run b0
  where
  b0 : Chain (Toff201 ∷ ι ∷ []) (ι ∷ Toff201 ∷ [])
  b0 = at 0 2 (ι ∷ Toff201 ∷ []) wn00429 ▸ done

-- pass [CSd23] [iI]: 3 steps
lem-pass-CSd23-vs-iI : ⟪ (CS23⁻ ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ CS23⁻ ∷ []) ⟫ʷ
lem-pass-CSd23-vs-iI = run b0
  where
  b0 : Chain (CS23⁻ ∷ ι ∷ []) (ι ∷ CS23⁻ ∷ [])
  b0 = at 1 1 (ι3 ∷ []) (trans (can-≈ (iI)) (sym (can-≈ ((iI ↑ ↑ ↑))))) ▸
       at 0 2 (ι3 ∷ CS23⁻ ∷ []) wn00430 ▸
       at 0 1 (ι ∷ []) (trans (can-≈ ((iI ↑ ↑ ↑))) (sym (can-≈ (iI)))) ▸ done

-- pass [Sd0] [CSd23]: 1 steps
lem-pass-Sd0-vs-CSd23 : ⟪ (S0⁻ ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ S0⁻ ∷ []) ⟫ʷ
lem-pass-Sd0-vs-CSd23 = run b0
  where
  b0 : Chain (S0⁻ ∷ CS23⁻ ∷ []) (CS23⁻ ∷ S0⁻ ∷ [])
  b0 = at 0 2 (CS23⁻ ∷ S0⁻ ∷ []) wn00431 ▸ done

-- pass [Sd3] [CSd23]: 1 steps
lem-pass-Sd3-vs-CSd23 : ⟪ (S3⁻ ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ S3⁻ ∷ []) ⟫ʷ
lem-pass-Sd3-vs-CSd23 = run b0
  where
  b0 : Chain (S3⁻ ∷ CS23⁻ ∷ []) (CS23⁻ ∷ S3⁻ ∷ [])
  b0 = at 0 2 (CS23⁻ ∷ S3⁻ ∷ []) wn00432 ▸ done

-- pass [CS03] [CSd23]: 15 steps
lem-pass-CS03-vs-CSd23 : ⟪ (CS03 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS03-vs-CSd23 = trans (run b0) (run b1)
  where
  b0 : Chain (CS03 ∷ CS23⁻ ∷ []) (Sw01 ∷ CS23⁻ ∷ CS13 ∷ Sw01 ∷ [])
  b0 = at 2 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 1 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 1 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 0 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 1 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (CS23⁻ ∷ CS13 ∷ []) wn00433 ▸ done

  b1 : Chain (Sw01 ∷ CS23⁻ ∷ CS13 ∷ Sw01 ∷ []) (CS23⁻ ∷ CS03 ∷ [])
  b1 = at 0 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 2 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 3 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00031 ▸ done

-- pass [CS23] [iI Sd0 Sd3 CS03]: 23 steps
lem-pass-CS23-vs-iI-Sd0-Sd3-CS03 : ⟪ (CS23 ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ CS23 ∷ []) ⟫ʷ
lem-pass-CS23-vs-iI-Sd0-Sd3-CS03 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS23 ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ []) (CS23 ∷ ι ∷ Sw01 ∷ S1⁻ ∷ S3⁻ ∷ CS13 ∷ Sw01 ∷ [])
  b0 = at 5 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 5 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 4 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw01 ∷ S3⁻ ∷ []) (sym (low-comm (Swap) (((S • S • S) ↑)))) ▸
       at 2 2 (Sw01 ∷ S1⁻ ∷ []) wn00434 ▸ done

  b1 : Chain (CS23 ∷ ι ∷ Sw01 ∷ S1⁻ ∷ S3⁻ ∷ CS13 ∷ Sw01 ∷ []) (ι ∷ S0⁻ ∷ S3⁻ ∷ Sw01 ∷ CS13 ∷ CS23 ∷ Sw01 ∷ [])
  b1 = at 1 2 (Sw01 ∷ ι ∷ []) wn00435 ▸
       at 0 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 2 1 (ι3 ∷ []) (trans (can-≈ (iI)) (sym (can-≈ ((iI ↑ ↑ ↑))))) ▸
       at 1 5 (ι3 ∷ S1⁻ ∷ S3⁻ ∷ CS13 ∷ CS23 ∷ []) wn00436 ▸
       at 1 1 (ι ∷ []) (trans (can-≈ ((iI ↑ ↑ ↑))) (sym (can-≈ (iI)))) ▸
       at 0 2 (ι ∷ Sw01 ∷ []) wn00437 ▸
       at 1 2 (S0⁻ ∷ Sw01 ∷ []) wn00316 ▸
       at 2 2 (S3⁻ ∷ Sw01 ∷ []) (low-comm (Swap) (((S • S • S) ↑))) ▸ done

  b2 : Chain (ι ∷ S0⁻ ∷ S3⁻ ∷ Sw01 ∷ CS13 ∷ CS23 ∷ Sw01 ∷ []) (ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ CS23 ∷ [])
  b2 = at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 4 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 3 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 5 2 [] wn00031 ▸ done

-- pass [TOFF201] [Sd0]: 1 steps
lem-pass-TOFF201-vs-Sd0 : ⟪ (Toff201 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ Toff201 ∷ []) ⟫ʷ
lem-pass-TOFF201-vs-Sd0 = run b0
  where
  b0 : Chain (Toff201 ∷ S0⁻ ∷ []) (S0⁻ ∷ Toff201 ∷ [])
  b0 = at 0 2 (S0⁻ ∷ Toff201 ∷ []) wn00438 ▸ done

-- pass [TOFF201] [Sd3]: 1 steps
lem-pass-TOFF201-vs-Sd3 : ⟪ (Toff201 ∷ S3⁻ ∷ []) ⟫ʷ ≈ ⟪ (S3⁻ ∷ Toff201 ∷ []) ⟫ʷ
lem-pass-TOFF201-vs-Sd3 = run b0
  where
  b0 : Chain (Toff201 ∷ S3⁻ ∷ []) (S3⁻ ∷ Toff201 ∷ [])
  b0 = at 0 2 (S3⁻ ∷ Toff201 ∷ []) (low₃-comm (Toffᵗ) ((S • S • S))) ▸ done

-- pass [CSd23] [iI Sd0 Sd3 CS03]: 23 steps
lem-pass-CSd23-vs-iI-Sd0-Sd3-CS03 : ⟪ (CS23⁻ ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ CS23⁻ ∷ []) ⟫ʷ
lem-pass-CSd23-vs-iI-Sd0-Sd3-CS03 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS23⁻ ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ []) (CS23⁻ ∷ ι ∷ Sw01 ∷ S1⁻ ∷ S3⁻ ∷ CS13 ∷ Sw01 ∷ [])
  b0 = at 5 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 5 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 4 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw01 ∷ S3⁻ ∷ []) (sym (low-comm (Swap) (((S • S • S) ↑)))) ▸
       at 2 2 (Sw01 ∷ S1⁻ ∷ []) wn00434 ▸ done

  b1 : Chain (CS23⁻ ∷ ι ∷ Sw01 ∷ S1⁻ ∷ S3⁻ ∷ CS13 ∷ Sw01 ∷ []) (ι ∷ S0⁻ ∷ S3⁻ ∷ Sw01 ∷ CS13 ∷ CS23⁻ ∷ Sw01 ∷ [])
  b1 = at 1 2 (Sw01 ∷ ι ∷ []) wn00435 ▸
       at 0 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 2 1 (ι3 ∷ []) (trans (can-≈ (iI)) (sym (can-≈ ((iI ↑ ↑ ↑))))) ▸
       at 1 5 (ι3 ∷ S1⁻ ∷ S3⁻ ∷ CS13 ∷ CS23⁻ ∷ []) wn00439 ▸
       at 1 1 (ι ∷ []) (trans (can-≈ ((iI ↑ ↑ ↑))) (sym (can-≈ (iI)))) ▸
       at 0 2 (ι ∷ Sw01 ∷ []) wn00437 ▸
       at 1 2 (S0⁻ ∷ Sw01 ∷ []) wn00316 ▸
       at 2 2 (S3⁻ ∷ Sw01 ∷ []) (low-comm (Swap) (((S • S • S) ↑))) ▸ done

  b2 : Chain (ι ∷ S0⁻ ∷ S3⁻ ∷ Sw01 ∷ CS13 ∷ CS23⁻ ∷ Sw01 ∷ []) (ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ CS23⁻ ∷ [])
  b2 = at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 4 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 3 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 5 2 [] wn00031 ▸ done

-- pass [CS23] [S2]: 1 steps
lem-pass-CS23-vs-S2 : ⟪ (CS23 ∷ S2 ∷ []) ⟫ʷ ≈ ⟪ (S2 ∷ CS23 ∷ []) ⟫ʷ
lem-pass-CS23-vs-S2 = run b0
  where
  b0 : Chain (CS23 ∷ S2 ∷ []) (S2 ∷ CS23 ∷ [])
  b0 = at 0 2 (S2 ∷ CS23 ∷ []) wn00440 ▸ done

-- pass [CS23] [Sd2]: 1 steps
lem-pass-CS23-vs-Sd2 : ⟪ (CS23 ∷ S2⁻ ∷ []) ⟫ʷ ≈ ⟪ (S2⁻ ∷ CS23 ∷ []) ⟫ʷ
lem-pass-CS23-vs-Sd2 = run b0
  where
  b0 : Chain (CS23 ∷ S2⁻ ∷ []) (S2⁻ ∷ CS23 ∷ [])
  b0 = at 0 2 (S2⁻ ∷ CS23 ∷ []) wn00441 ▸ done

-- pass [CS23] [S1]: 1 steps
lem-pass-CS23-vs-S1 : ⟪ (CS23 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ CS23 ∷ []) ⟫ʷ
lem-pass-CS23-vs-S1 = run b0
  where
  b0 : Chain (CS23 ∷ S1 ∷ []) (S1 ∷ CS23 ∷ [])
  b0 = at 0 2 (S1 ∷ CS23 ∷ []) wn00442 ▸ done

-- pass [CS23] [Sd1]: 1 steps
lem-pass-CS23-vs-Sd1 : ⟪ (CS23 ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ CS23 ∷ []) ⟫ʷ
lem-pass-CS23-vs-Sd1 = run b0
  where
  b0 : Chain (CS23 ∷ S1⁻ ∷ []) (S1⁻ ∷ CS23 ∷ [])
  b0 = at 0 2 (S1⁻ ∷ CS23 ∷ []) wn00443 ▸ done

-- pass [CCZ012] [CS01]: 1 steps
lem-pass-CCZ012-vs-CS01 : ⟪ (CCZ012 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CCZ012 ∷ []) ⟫ʷ
lem-pass-CCZ012-vs-CS01 = run b0
  where
  b0 : Chain (CCZ012 ∷ CS01 ∷ []) (CS01 ∷ CCZ012 ∷ [])
  b0 = at 0 2 (CS01 ∷ CCZ012 ∷ []) wn00444 ▸ done

-- pass [S2] [CSd23]: 1 steps
lem-pass-S2-vs-CSd23 : ⟪ (S2 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ S2 ∷ []) ⟫ʷ
lem-pass-S2-vs-CSd23 = run b0
  where
  b0 : Chain (S2 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ S2 ∷ [])
  b0 = at 0 2 (CS23⁻ ∷ S2 ∷ []) wn00445 ▸ done

-- pass [CCZ012] [CSd01]: 1 steps
lem-pass-CCZ012-vs-CSd01 : ⟪ (CCZ012 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ CCZ012 ∷ []) ⟫ʷ
lem-pass-CCZ012-vs-CSd01 = run b0
  where
  b0 : Chain (CCZ012 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CCZ012 ∷ [])
  b0 = at 0 2 (CS01⁻ ∷ CCZ012 ∷ []) wn00446 ▸ done

-- pass [Sd2] [CSd23]: 1 steps
lem-pass-Sd2-vs-CSd23 : ⟪ (S2⁻ ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ S2⁻ ∷ []) ⟫ʷ
lem-pass-Sd2-vs-CSd23 = run b0
  where
  b0 : Chain (S2⁻ ∷ CS23⁻ ∷ []) (CS23⁻ ∷ S2⁻ ∷ [])
  b0 = at 0 2 (CS23⁻ ∷ S2⁻ ∷ []) wn00447 ▸ done

-- pass [X3 CK30 X3] [TOFF203]: 75 steps
lem-pass-X3-CK30-X3-vs-TOFF203 : ⟪ (X3 ∷ CK30 ∷ X3 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ X3 ∷ CK30 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CK30-X3-vs-TOFF203 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (run b9)))))))))
  where
  b0 : Chain (X3 ∷ CK30 ∷ X3 ∷ Toff203 ∷ []) (X3 ∷ CK30 ∷ X3 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ K2 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ [])
  b0 = at 4 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 3 1 (Sw01 ∷ Toff213 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 4 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 5 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 6 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 7 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸ done

  b1 : Chain (X3 ∷ CK30 ∷ X3 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ K2 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ []) (X3 ∷ CK30 ∷ X3 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ Sw01 ∷ Sw01 ∷ [])
  b1 = at 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 10 2 (ι ∷ Sw01 ∷ []) wn00122 ▸
       at 11 2 [] wn00031 ▸ done

  b2 : Chain (X3 ∷ CK30 ∷ X3 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ Sw01 ∷ Sw01 ∷ []) (X3 ∷ CK30 ∷ X3 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ Sw01 ∷ [])
  b2 = at 10 2 (Sw01 ∷ ι1 ∷ []) wn00127 ▸
       at 9 2 (Sw01 ∷ K2 ∷ []) (sym (low-comm (Swap) (K))) ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 9 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 8 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 9 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸ done

  b3 : Chain (X3 ∷ CK30 ∷ X3 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ Sw01 ∷ []) (X3 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw01 ∷ X3 ∷ Toff213 ∷ Sw01 ∷ [])
  b3 = at 6 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 5 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸
       at 4 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 3 2 (Sw01 ∷ K2 ∷ []) (sym (low-comm (Swap) (K))) ▸
       at 4 8 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) wn00334 ▸
       at 4 8 (Toff213 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸
       at 1 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (X3 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw01 ∷ X3 ∷ Toff213 ∷ Sw01 ∷ []) (K2 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ X3 ∷ CK31 ∷ X3 ∷ Sw01 ∷ [])
  b4 = at 3 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 2 2 (Sw01 ∷ CK21 ∷ []) wn00140 ▸
       at 1 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 2 3 (CK31 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸
       at 1 4 (Toff213 ∷ X3 ∷ CK31 ∷ X3 ∷ []) wn00448 ▸
       at 1 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸ done

  b5 : Chain (K2 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ X3 ∷ CK31 ∷ X3 ∷ Sw01 ∷ []) (K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ K2 ∷ ι1 ∷ X3 ∷ CK31 ∷ X3 ∷ Sw01 ∷ [])
  b5 = at 1 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 2 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 3 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 4 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b6 : Chain (K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ K2 ∷ ι1 ∷ X3 ∷ CK31 ∷ X3 ∷ Sw01 ∷ []) (Sw01 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ Sw01 ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ Sw01 ∷ X3 ∷ CK31 ∷ X3 ∷ Sw01 ∷ [])
  b6 = at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 7 2 (ι ∷ Sw01 ∷ []) wn00122 ▸
       at 0 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 1 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 2 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 3 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 4 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸ done

  b7 : Chain (Sw01 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ Sw01 ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ Sw01 ∷ X3 ∷ CK31 ∷ X3 ∷ Sw01 ∷ []) (Sw01 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ X3 ∷ CK31 ∷ X3 ∷ Sw01 ∷ [])
  b7 = at 5 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 8 2 (ι1 ∷ Sw01 ∷ []) wn00124 ▸ done

  b8 : Chain (Sw01 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ X3 ∷ CK31 ∷ X3 ∷ Sw01 ∷ []) (Toff203 ∷ X3 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw01 ∷ X3 ∷ Sw01 ∷ [])
  b8 = at 1 8 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) wn00334 ▸
       at 1 8 (Toff213 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff203 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸
       at 3 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 3 2 (CK20 ∷ Sw01 ∷ []) wn00142 ▸
       at 4 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b9 : Chain (Toff203 ∷ X3 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw01 ∷ X3 ∷ Sw01 ∷ []) (Toff203 ∷ X3 ∷ CK30 ∷ X3 ∷ [])
  b9 = at 2 3 (CK30 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸
       at 4 2 [] wn00031 ▸ done

-- pass [X3 CS30 X3] [TOFF203]: 75 steps
lem-pass-X3-CS30-X3-vs-TOFF203 : ⟪ (X3 ∷ CS03 ∷ X3 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ X3 ∷ CS03 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS30-X3-vs-TOFF203 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (run b9)))))))))
  where
  b0 : Chain (X3 ∷ CS03 ∷ X3 ∷ Toff203 ∷ []) (X3 ∷ CS03 ∷ X3 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ K2 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ [])
  b0 = at 4 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 3 1 (Sw01 ∷ Toff213 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 4 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 5 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 6 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 7 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸ done

  b1 : Chain (X3 ∷ CS03 ∷ X3 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ K2 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ []) (X3 ∷ CS03 ∷ X3 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ Sw01 ∷ Sw01 ∷ [])
  b1 = at 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 10 2 (ι ∷ Sw01 ∷ []) wn00122 ▸
       at 11 2 [] wn00031 ▸ done

  b2 : Chain (X3 ∷ CS03 ∷ X3 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ Sw01 ∷ Sw01 ∷ []) (X3 ∷ CS03 ∷ X3 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ Sw01 ∷ [])
  b2 = at 10 2 (Sw01 ∷ ι1 ∷ []) wn00127 ▸
       at 9 2 (Sw01 ∷ K2 ∷ []) (sym (low-comm (Swap) (K))) ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 9 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 8 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 9 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸ done

  b3 : Chain (X3 ∷ CS03 ∷ X3 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ Sw01 ∷ []) (X3 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ X3 ∷ Toff213 ∷ Sw01 ∷ [])
  b3 = at 6 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 5 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸
       at 4 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 3 2 (Sw01 ∷ K2 ∷ []) (sym (low-comm (Swap) (K))) ▸
       at 4 8 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) wn00334 ▸
       at 4 8 (Toff213 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸
       at 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (X3 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ X3 ∷ Toff213 ∷ Sw01 ∷ []) (K2 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ X3 ∷ CS13 ∷ X3 ∷ Sw01 ∷ [])
  b4 = at 3 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 2 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 1 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸
       at 1 4 (Toff213 ∷ X3 ∷ CS13 ∷ X3 ∷ []) wn00449 ▸
       at 1 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸ done

  b5 : Chain (K2 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ X3 ∷ CS13 ∷ X3 ∷ Sw01 ∷ []) (K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ K2 ∷ ι1 ∷ X3 ∷ CS13 ∷ X3 ∷ Sw01 ∷ [])
  b5 = at 1 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 2 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 3 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 4 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b6 : Chain (K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ K2 ∷ ι1 ∷ X3 ∷ CS13 ∷ X3 ∷ Sw01 ∷ []) (Sw01 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ Sw01 ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ Sw01 ∷ X3 ∷ CS13 ∷ X3 ∷ Sw01 ∷ [])
  b6 = at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 7 2 (ι ∷ Sw01 ∷ []) wn00122 ▸
       at 0 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 1 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 2 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 3 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 4 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸ done

  b7 : Chain (Sw01 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ Sw01 ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ Sw01 ∷ X3 ∷ CS13 ∷ X3 ∷ Sw01 ∷ []) (Sw01 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ X3 ∷ CS13 ∷ X3 ∷ Sw01 ∷ [])
  b7 = at 5 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 8 2 (ι1 ∷ Sw01 ∷ []) wn00124 ▸ done

  b8 : Chain (Sw01 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ X3 ∷ CS13 ∷ X3 ∷ Sw01 ∷ []) (Toff203 ∷ X3 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ X3 ∷ Sw01 ∷ [])
  b8 = at 1 8 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) wn00334 ▸
       at 1 8 (Toff213 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff203 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸
       at 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 3 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 4 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b9 : Chain (Toff203 ∷ X3 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ X3 ∷ Sw01 ∷ []) (Toff203 ∷ X3 ∷ CS03 ∷ X3 ∷ [])
  b9 = at 2 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸
       at 4 2 [] wn00031 ▸ done

-- pass [X3 CSd30 X3] [TOFF203]: 75 steps
lem-pass-X3-CSd30-X3-vs-TOFF203 : ⟪ (X3 ∷ CS03⁻ ∷ X3 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd30-X3-vs-TOFF203 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (run b9)))))))))
  where
  b0 : Chain (X3 ∷ CS03⁻ ∷ X3 ∷ Toff203 ∷ []) (X3 ∷ CS03⁻ ∷ X3 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ K2 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ [])
  b0 = at 4 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 3 1 (Sw01 ∷ Toff213 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 4 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 5 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 6 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 7 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸ done

  b1 : Chain (X3 ∷ CS03⁻ ∷ X3 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ K2 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ []) (X3 ∷ CS03⁻ ∷ X3 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ Sw01 ∷ Sw01 ∷ [])
  b1 = at 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 10 2 (ι ∷ Sw01 ∷ []) wn00122 ▸
       at 11 2 [] wn00031 ▸ done

  b2 : Chain (X3 ∷ CS03⁻ ∷ X3 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ Sw01 ∷ Sw01 ∷ []) (X3 ∷ CS03⁻ ∷ X3 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ Sw01 ∷ [])
  b2 = at 10 2 (Sw01 ∷ ι1 ∷ []) wn00127 ▸
       at 9 2 (Sw01 ∷ K2 ∷ []) (sym (low-comm (Swap) (K))) ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 9 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 8 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 9 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸ done

  b3 : Chain (X3 ∷ CS03⁻ ∷ X3 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ Sw01 ∷ []) (X3 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Sw01 ∷ X3 ∷ Toff213 ∷ Sw01 ∷ [])
  b3 = at 6 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 5 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸
       at 4 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 3 2 (Sw01 ∷ K2 ∷ []) (sym (low-comm (Swap) (K))) ▸
       at 4 8 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) wn00334 ▸
       at 4 8 (Toff213 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸
       at 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (X3 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Sw01 ∷ X3 ∷ Toff213 ∷ Sw01 ∷ []) (K2 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ Sw01 ∷ [])
  b4 = at 3 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 2 2 (Sw01 ∷ CS12⁻ ∷ []) wn00076 ▸
       at 1 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 2 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸
       at 1 4 (Toff213 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) wn00450 ▸
       at 1 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸ done

  b5 : Chain (K2 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ Sw01 ∷ []) (K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ K2 ∷ ι1 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ Sw01 ∷ [])
  b5 = at 1 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 2 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 3 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 4 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b6 : Chain (K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ K2 ∷ ι1 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ Sw01 ∷ []) (Sw01 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ Sw01 ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ Sw01 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ Sw01 ∷ [])
  b6 = at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 7 2 (ι ∷ Sw01 ∷ []) wn00122 ▸
       at 0 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 1 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 2 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 3 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 4 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸ done

  b7 : Chain (Sw01 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ Sw01 ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ Sw01 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ Sw01 ∷ []) (Sw01 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ Sw01 ∷ [])
  b7 = at 5 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 8 2 (ι1 ∷ Sw01 ∷ []) wn00124 ▸ done

  b8 : Chain (Sw01 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ Sw01 ∷ []) (Toff203 ∷ X3 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Sw01 ∷ X3 ∷ Sw01 ∷ [])
  b8 = at 1 8 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) wn00334 ▸
       at 1 8 (Toff213 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff203 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸
       at 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 3 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸
       at 4 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b9 : Chain (Toff203 ∷ X3 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Sw01 ∷ X3 ∷ Sw01 ∷ []) (Toff203 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ [])
  b9 = at 2 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸
       at 4 2 [] wn00031 ▸ done

-- pass [X3 CKd30 X3] [TOFF203]: 75 steps
lem-pass-X3-CKd30-X3-vs-TOFF203 : ⟪ (X3 ∷ CK30⁻ ∷ X3 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd30-X3-vs-TOFF203 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (run b9)))))))))
  where
  b0 : Chain (X3 ∷ CK30⁻ ∷ X3 ∷ Toff203 ∷ []) (X3 ∷ CK30⁻ ∷ X3 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ K2 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ [])
  b0 = at 4 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 3 1 (Sw01 ∷ Toff213 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 4 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 5 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 6 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 7 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸ done

  b1 : Chain (X3 ∷ CK30⁻ ∷ X3 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ K2 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ []) (X3 ∷ CK30⁻ ∷ X3 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ Sw01 ∷ Sw01 ∷ [])
  b1 = at 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 10 2 (ι ∷ Sw01 ∷ []) wn00122 ▸
       at 11 2 [] wn00031 ▸ done

  b2 : Chain (X3 ∷ CK30⁻ ∷ X3 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ Sw01 ∷ Sw01 ∷ []) (X3 ∷ CK30⁻ ∷ X3 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ Sw01 ∷ [])
  b2 = at 10 2 (Sw01 ∷ ι1 ∷ []) wn00127 ▸
       at 9 2 (Sw01 ∷ K2 ∷ []) (sym (low-comm (Swap) (K))) ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 9 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 8 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 9 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸ done

  b3 : Chain (X3 ∷ CK30⁻ ∷ X3 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ Sw01 ∷ []) (X3 ∷ Sw23 ∷ CK20⁻ ∷ Sw23 ∷ Sw01 ∷ X3 ∷ Toff213 ∷ Sw01 ∷ [])
  b3 = at 6 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 5 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸
       at 4 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 3 2 (Sw01 ∷ K2 ∷ []) (sym (low-comm (Swap) (K))) ▸
       at 4 8 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) wn00334 ▸
       at 4 8 (Toff213 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸
       at 1 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (X3 ∷ Sw23 ∷ CK20⁻ ∷ Sw23 ∷ Sw01 ∷ X3 ∷ Toff213 ∷ Sw01 ∷ []) (K2 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ Sw01 ∷ [])
  b4 = at 3 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 2 2 (Sw01 ∷ CK21⁻ ∷ []) wn00137 ▸
       at 1 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 2 3 (CK31⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸
       at 1 4 (Toff213 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) wn00451 ▸
       at 1 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸ done

  b5 : Chain (K2 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ Sw01 ∷ []) (K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ K2 ∷ ι1 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ Sw01 ∷ [])
  b5 = at 1 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 2 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 3 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 4 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b6 : Chain (K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ K2 ∷ ι1 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ Sw01 ∷ []) (Sw01 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ Sw01 ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ Sw01 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ Sw01 ∷ [])
  b6 = at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 7 2 (ι ∷ Sw01 ∷ []) wn00122 ▸
       at 0 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 1 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 2 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 3 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 4 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸ done

  b7 : Chain (Sw01 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ Sw01 ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ Sw01 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ Sw01 ∷ []) (Sw01 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ Sw01 ∷ [])
  b7 = at 5 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 8 2 (ι1 ∷ Sw01 ∷ []) wn00124 ▸ done

  b8 : Chain (Sw01 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ Sw01 ∷ []) (Toff203 ∷ X3 ∷ Sw23 ∷ CK20⁻ ∷ Sw23 ∷ Sw01 ∷ X3 ∷ Sw01 ∷ [])
  b8 = at 1 8 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) wn00334 ▸
       at 1 8 (Toff213 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff203 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸
       at 3 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 3 2 (CK20⁻ ∷ Sw01 ∷ []) wn00139 ▸
       at 4 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b9 : Chain (Toff203 ∷ X3 ∷ Sw23 ∷ CK20⁻ ∷ Sw23 ∷ Sw01 ∷ X3 ∷ Sw01 ∷ []) (Toff203 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ [])
  b9 = at 2 3 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸
       at 4 2 [] wn00031 ▸ done

-- b2g 0111R1: 4 steps
lem-b2g-0111R1 : ⟪ (X1 ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-b2g-0111R1 = run b0
  where
  b0 : Chain (X1 ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ X3 ∷ [])
  b0 = at 0 2 (X2 ∷ X1 ∷ []) (low-comm ((X ↑)) (X)) ▸
       at 1 2 (X3 ∷ X1 ∷ []) (low-comm ((X ↑)) ((X ↑))) ▸
       at 2 3 (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ []) wn00452 ▸
       at 10 3 (S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) wn00453 ▸ done

-- b2g 1111R0: 5 steps
lem-b2g-1111R0 : ⟪ (X0 ∷ X1 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X0 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-b2g-1111R0 = run b0
  where
  b0 : Chain (X0 ∷ X1 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X0 ∷ X1 ∷ X2 ∷ X3 ∷ []) (X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ X2 ∷ X3 ∷ [])
  b0 = at 0 2 (X1 ∷ X0 ∷ []) (low₁-comm (X) (X)) ▸
       at 1 2 (X2 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑))) ▸
       at 2 2 (X3 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑ ↑))) ▸
       at 3 3 (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) wn00391 ▸
       at 11 3 (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) wn00392 ▸ done

-- pass [X1 CSd10 X1] [TOFF012]: 1 steps
lem-pass-X1-CSd10-X1-vs-TOFF012 : ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CSd10-X1-vs-TOFF012 = run b0
  where
  b0 : Chain (X1 ∷ CS01⁻ ∷ X1 ∷ Toff012 ∷ []) (Toff012 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ [])
  b0 = at 0 4 (Toff012 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) wn00454 ▸ done

-- pass [X1 CSd10 X1] [CS03]: 13 steps
lem-pass-X1-CSd10-X1-vs-CS03 : ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CSd10-X1-vs-CS03 = trans (run b0) (run b1)
  where
  b0 : Chain (X1 ∷ CS01⁻ ∷ X1 ∷ CS03 ∷ []) (Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ Sw23 ∷ [])
  b0 = at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 2 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 1 2 (Sw23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (Swap)) ▸
       at 0 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 1 4 (CS02 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) wn00455 ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b1 : Chain (Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ Sw23 ∷ []) (CS03 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ [])
  b1 = at 0 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 2 2 (CS01⁻ ∷ Sw23 ∷ []) (sym (low-comm ((CS • CS • CS)) (Swap))) ▸
       at 3 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 4 2 [] wn00003 ▸ done

-- pass [X1 CSd10 X1] [CSd03]: 13 steps
lem-pass-X1-CSd10-X1-vs-CSd03 : ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CSd10-X1-vs-CSd03 = trans (run b0) (run b1)
  where
  b0 : Chain (X1 ∷ CS01⁻ ∷ X1 ∷ CS03⁻ ∷ []) (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Sw23 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ Sw23 ∷ [])
  b0 = at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 2 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 1 2 (Sw23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (Swap)) ▸
       at 0 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 1 4 (CS02⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) wn00456 ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b1 : Chain (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Sw23 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ Sw23 ∷ []) (CS03⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ [])
  b1 = at 0 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 2 2 (CS01⁻ ∷ Sw23 ∷ []) (sym (low-comm ((CS • CS • CS)) (Swap))) ▸
       at 3 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 4 2 [] wn00003 ▸ done

-- comm CCZ012 CSd23: 19 steps
lem-comm-CCZ012-CSd23 : ⟪ (CCZ012 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ CCZ012 ∷ []) ⟫ʷ
lem-comm-CCZ012-CSd23 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CCZ012 ∷ CS23⁻ ∷ []) (CS01 ∷ CX20 ∷ CS01⁻ ∷ CS23⁻ ∷ CX20 ∷ Sw01 ∷ Sw01 ∷ CS12 ∷ [])
  b0 = at 0 1 (CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ []) wn00100 ▸
       at 4 2 (CS23⁻ ∷ CS12 ∷ []) wn00416 ▸
       at 5 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 4 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 3 2 (Sw01 ∷ CX21 ∷ []) wn00006 ▸
       at 4 2 (CS23⁻ ∷ CX21 ∷ []) wn00457 ▸
       at 3 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 4 2 (CX20 ∷ Sw01 ∷ []) wn00039 ▸ done

  b1 : Chain (CS01 ∷ CX20 ∷ CS01⁻ ∷ CS23⁻ ∷ CX20 ∷ Sw01 ∷ Sw01 ∷ CS12 ∷ []) (CS01 ∷ CS23⁻ ∷ CX20 ∷ Sw01 ∷ Sw01 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ [])
  b1 = at 5 2 [] wn00031 ▸
       at 2 2 (CS23⁻ ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) ((CS • CS • CS))) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 2 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 1 2 (Sw01 ∷ CX21 ∷ []) wn00006 ▸
       at 2 2 (CS23⁻ ∷ CX21 ∷ []) wn00457 ▸
       at 1 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 2 2 (CX20 ∷ Sw01 ∷ []) wn00039 ▸ done

  b2 : Chain (CS01 ∷ CS23⁻ ∷ CX20 ∷ Sw01 ∷ Sw01 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ []) (CS23⁻ ∷ CCZ012 ∷ [])
  b2 = at 3 2 [] wn00031 ▸
       at 0 2 (CS23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((CS • CS • CS))) ▸
       at 1 5 (CCZ012 ∷ []) wn00104 ▸ done

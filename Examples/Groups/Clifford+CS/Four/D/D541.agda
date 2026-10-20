{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D541 where

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
open import Examples.Groups.Clifford+CS.Four.Wins.W01 using (wn00001 ; wn00003 ; wn00005 ; wn00007 ; wn00024 ; wn00025 ; wn00026 ; wn00027 ; wn00029 ; wn00030 ; wn00031 ; wn00033 ; wn00045 ; wn00074 ; wn00076 ; wn00118 ; wn00121 ; wn00122 ; wn00123 ; wn00124 ; wn00125 ; wn00127 ; wn00128)
open import Examples.Groups.Clifford+CS.Four.Wins.W02 using (wn00227 ; wn00231)
open import Examples.Groups.Clifford+CS.Four.Wins.W27 using (wn01342 ; wn01357 ; wn01358 ; wn01413)
open import Examples.Groups.Clifford+CS.Four.Wins.W28 using (wn01437 ; wn01448 ; wn01449 ; wn01469 ; wn01471 ; wn01472 ; wn01473 ; wn01474 ; wn01475 ; wn01476 ; wn01477 ; wn01478 ; wn01479 ; wn01480 ; wn01481 ; wn01482 ; wn01483 ; wn01484 ; wn01485 ; wn01486 ; wn01487 ; wn01488 ; wn01489 ; wn01490 ; wn01491 ; wn01492 ; wn01493 ; wn01494 ; wn01495 ; wn01496 ; wn01497 ; wn01498 ; wn01499 ; wn01500 ; wn01501 ; wn01502 ; wn01503 ; wn01504 ; wn01505 ; wn01506 ; wn01507 ; wn01508)
open import Examples.Groups.Clifford+CS.Four.D.D013 using (lem-pass-CCZ023-vs-CSd23 ; lem-pass-CCZ023-vs-CZ23 ; lem-pass-CSd03-vs-CS01 ; lem-pass-CSd03-vs-CSd01 ; lem-pass-CSd23-vs-CS01)
open import Examples.Groups.Clifford+CS.Four.D.D510 using (lem-pass-CCZ123-vs-CSd03 ; lem-pass-X3-CKd30-X3-vs-TOFF012-CS03-TOFF012-CSd03)
open import Examples.Groups.Clifford+CS.Four.D.D513 using (lem-pass-CCZ023-vs-CS01 ; lem-pass-CSd03-vs-TOFF103-CS12-TOFF103-CSd12 ; lem-pass-S0-vs-TOFF102-CS13-TOFF102-CSd13 ; lem-pass-S0-vs-TOFF103-CS12-TOFF103-CSd12 ; lem-pass-S0-vs-TOFF123-CS01-TOFF123-CSd01 ; lem-pass-X2-CK20-X2-vs-TOFF102-CS13-TOFF102-CSd13 ; lem-pass-X2-CK21-X2-vs-CS03-TOFF012-CSd03-TOFF012 ; lem-pass-X2-CKd20-X2-vs-TOFF102-CS13-TOFF102-CSd13 ; lem-pass-X2-CKd21-X2-vs-CS03-TOFF012-CSd03-TOFF012 ; lem-pass-X2-CS20-X2-vs-TOFF102-CS13-TOFF102-CSd13 ; lem-pass-X2-CS21-X2-vs-CS03-TOFF012-CSd03-TOFF012 ; lem-pass-X2-CS21-X2-vs-TOFF102-CS13-TOFF102-CSd13 ; lem-pass-X2-CSd20-X2-vs-TOFF012-CS03-TOFF012-CSd03 ; lem-pass-X2-CSd20-X2-vs-TOFF102-CS13-TOFF102-CSd13 ; lem-pass-X2-CSd21-X2-vs-CS03-TOFF012-CSd03-TOFF012)

-- pass [CSd03] [TOFF023 CS01 TOFF023 CSd01]: 417 steps
lem-pass-CSd03-vs-TOFF023-CS01-TOFF023-CSd01 : ⟪ (CS03⁻ ∷ Toff023 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-CSd03-vs-TOFF023-CS01-TOFF023-CSd01 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (trans (run b38) (trans (run b39) (trans (run b40) (trans (run b41) (trans (run b42) (trans (run b43) (trans (run b44) (trans (run b45) (trans (run b46) (trans (run b47) (trans (run b48) (trans (run b49) (trans (run b50) (trans (run b51) (run b52))))))))))))))))))))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (CS03⁻ ∷ Toff023 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ []) (CS03⁻ ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ [])
  b0 = at 2 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 1 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 2 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 3 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 4 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 5 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸ done

  b1 : Chain (CS03⁻ ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ []) (CS03⁻ ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ Sw01 ∷ Sw01 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ [])
  b1 = at 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 8 2 (ι ∷ Sw01 ∷ []) wn00122 ▸
       at 9 2 [] wn00031 ▸ done

  b2 : Chain (CS03⁻ ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ Sw01 ∷ Sw01 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ []) (CS03⁻ ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ [])
  b2 = at 8 2 (Sw01 ∷ ι1 ∷ []) wn00127 ▸
       at 7 2 (Sw01 ∷ K1 ∷ []) wn00118 ▸
       at 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 7 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 6 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 7 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸ done

  b3 : Chain (CS03⁻ ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ []) (Sw23 ∷ CS02⁻ ∷ Sw01 ∷ Sw23 ∷ Toff123 ∷ Sw01 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ [])
  b3 = at 4 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 3 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸
       at 2 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 1 2 (Sw01 ∷ K1 ∷ []) wn00118 ▸
       at 2 8 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) wn00125 ▸
       at 2 8 (Toff123 ∷ []) (by-assoc Eq.refl) ▸
       at 0 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b4 : Chain (Sw23 ∷ CS02⁻ ∷ Sw01 ∷ Sw23 ∷ Toff123 ∷ Sw01 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ []) (K0 ∷ CS23 ∷ CX02 ∷ Sw01 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ CS13⁻ ∷ CS23⁻ ∷ CCZ123 ∷ Sw01 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ [])
  b4 = at 1 2 (Sw01 ∷ CS12⁻ ∷ []) wn00076 ▸
       at 0 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 1 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Toff123 ∷ CS13⁻ ∷ CS23⁻ ∷ CCZ123 ∷ []) wn01471 ▸
       at 1 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 1 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 2 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸ done

  b5 : Chain (K0 ∷ CS23 ∷ CX02 ∷ Sw01 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ CS13⁻ ∷ CS23⁻ ∷ CCZ123 ∷ Sw01 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ []) (K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ Sw01 ∷ ι1 ∷ CS13⁻ ∷ CS23⁻ ∷ CCZ123 ∷ Sw01 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ [])
  b5 = at 3 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 4 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸ done

  b6 : Chain (K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ Sw01 ∷ ι1 ∷ CS13⁻ ∷ CS23⁻ ∷ CCZ123 ∷ Sw01 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ []) (Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw01 ∷ CS13⁻ ∷ CS23⁻ ∷ CCZ123 ∷ Sw01 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ [])
  b6 = at 7 2 (ι ∷ Sw01 ∷ []) wn00122 ▸
       at 0 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 1 2 (K1 ∷ Sw01 ∷ []) wn00123 ▸
       at 2 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 3 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 4 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 5 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b7 : Chain (Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw01 ∷ CS13⁻ ∷ CS23⁻ ∷ CCZ123 ∷ Sw01 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ []) (Sw01 ∷ Toff123 ∷ Sw01 ∷ Sw01 ∷ CS13⁻ ∷ CS23⁻ ∷ CCZ123 ∷ Sw01 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ [])
  b7 = at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K1 ∷ Sw01 ∷ []) wn00123 ▸
       at 8 2 (ι1 ∷ Sw01 ∷ []) wn00124 ▸
       at 1 8 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) wn00125 ▸
       at 1 8 (Toff123 ∷ []) (by-assoc Eq.refl) ▸ done

  b8 : Chain (Sw01 ∷ Toff123 ∷ Sw01 ∷ Sw01 ∷ CS13⁻ ∷ CS23⁻ ∷ CCZ123 ∷ Sw01 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS03⁻ ∷ CS23⁻ ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ [])
  b8 = at 0 3 (Toff023 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 2 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸
       at 3 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b9 : Chain (Toff023 ∷ CS03⁻ ∷ CS23⁻ ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS03⁻ ∷ CS23⁻ ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ [])
  b9 = at 3 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 4 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 5 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 6 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b10 : Chain (Toff023 ∷ CS03⁻ ∷ CS23⁻ ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS03⁻ ∷ CS23⁻ ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ Sw01 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ [])
  b10 = at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 4 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 5 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 6 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 7 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b11 : Chain (Toff023 ∷ CS03⁻ ∷ CS23⁻ ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ Sw01 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS03⁻ ∷ CS23⁻ ∷ CS01 ∷ CCZ023 ∷ Toff023 ∷ CS01⁻ ∷ [])
  b11 = at 9 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸
       at 4 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00031 ▸
       at 3 2 (CS01 ∷ CCZ023 ∷ []) (lem-pass-CCZ023-vs-CS01) ▸ done

  b12 : Chain (Toff023 ∷ CS03⁻ ∷ CS23⁻ ∷ CS01 ∷ CCZ023 ∷ Toff023 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ CS03⁻ ∷ CS23⁻ ∷ CCZ023 ∷ K0 ∷ CS23 ∷ CX02 ∷ Sw01 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CS01⁻ ∷ [])
  b12 = at 2 2 (CS01 ∷ CS23⁻ ∷ []) (lem-pass-CSd23-vs-CS01) ▸
       at 1 2 (CS01 ∷ CS03⁻ ∷ []) (lem-pass-CSd03-vs-CS01) ▸
       at 6 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 5 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 6 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 7 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸ done

  b13 : Chain (Toff023 ∷ CS01 ∷ CS03⁻ ∷ CS23⁻ ∷ CCZ023 ∷ K0 ∷ CS23 ∷ CX02 ∷ Sw01 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ CS03⁻ ∷ CS23⁻ ∷ CCZ023 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ Sw01 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CS01⁻ ∷ [])
  b13 = at 8 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 9 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 11 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 12 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸ done

  b14 : Chain (Toff023 ∷ CS01 ∷ CS03⁻ ∷ CS23⁻ ∷ CCZ023 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ Sw01 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ CS03⁻ ∷ CS23⁻ ∷ CCZ023 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ K1 ∷ ι1 ∷ Sw01 ∷ CS01⁻ ∷ [])
  b14 = at 12 2 (ι ∷ Sw01 ∷ []) wn00122 ▸
       at 13 2 [] wn00031 ▸
       at 12 2 (Sw01 ∷ ι1 ∷ []) wn00127 ▸
       at 11 2 (Sw01 ∷ K1 ∷ []) wn00118 ▸
       at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 11 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 10 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b15 : Chain (Toff023 ∷ CS01 ∷ CS03⁻ ∷ CS23⁻ ∷ CCZ023 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ K1 ∷ ι1 ∷ Sw01 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ CS03⁻ ∷ CS23⁻ ∷ CCZ023 ∷ Sw01 ∷ Toff123 ∷ Sw01 ∷ CS01⁻ ∷ [])
  b15 = at 11 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸
       at 8 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 7 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸
       at 6 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 5 2 (Sw01 ∷ K1 ∷ []) wn00118 ▸
       at 6 8 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) wn00125 ▸
       at 6 8 (Toff123 ∷ []) (by-assoc Eq.refl) ▸ done

  b16 : Chain (Toff023 ∷ CS01 ∷ CS03⁻ ∷ CS23⁻ ∷ CCZ023 ∷ Sw01 ∷ Toff123 ∷ Sw01 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ CS03⁻ ∷ CS23⁻ ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Toff123 ∷ Sw01 ∷ CS01⁻ ∷ [])
  b16 = at 4 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 5 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 6 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 7 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b17 : Chain (Toff023 ∷ CS01 ∷ CS03⁻ ∷ CS23⁻ ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Toff123 ∷ Sw01 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ CS03⁻ ∷ CS23⁻ ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Toff123 ∷ Sw01 ∷ CS01⁻ ∷ [])
  b17 = at 9 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00031 ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 9 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 8 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b18 : Chain (Toff023 ∷ CS01 ∷ CS03⁻ ∷ CS23⁻ ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Toff123 ∷ Sw01 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ CS03⁻ ∷ CS23⁻ ∷ Sw01 ∷ Toff123 ∷ CZ23 ∷ CCZ123 ∷ Sw01 ∷ CS01⁻ ∷ [])
  b18 = at 9 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸
       at 6 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 5 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸
       at 4 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 5 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸
       at 5 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Toff123 ∷ CZ23 ∷ CCZ123 ∷ []) wn01469 ▸ done

  b19 : Chain (Toff023 ∷ CS01 ∷ CS03⁻ ∷ CS23⁻ ∷ Sw01 ∷ Toff123 ∷ CZ23 ∷ CCZ123 ∷ Sw01 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ CS03⁻ ∷ CS23⁻ ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ K1 ∷ ι1 ∷ CZ23 ∷ CCZ123 ∷ Sw01 ∷ CS01⁻ ∷ [])
  b19 = at 5 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 5 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 6 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 7 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 8 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b20 : Chain (Toff023 ∷ CS01 ∷ CS03⁻ ∷ CS23⁻ ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ K1 ∷ ι1 ∷ CZ23 ∷ CCZ123 ∷ Sw01 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ CS03⁻ ∷ CS23⁻ ∷ Sw01 ∷ K1 ∷ CS23 ∷ Sw01 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ Sw01 ∷ CZ23 ∷ CCZ123 ∷ Sw01 ∷ CS01⁻ ∷ [])
  b20 = at 10 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 11 2 (ι ∷ Sw01 ∷ []) wn00122 ▸
       at 4 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 5 2 (K1 ∷ Sw01 ∷ []) wn00123 ▸
       at 6 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸ done

  b21 : Chain (Toff023 ∷ CS01 ∷ CS03⁻ ∷ CS23⁻ ∷ Sw01 ∷ K1 ∷ CS23 ∷ Sw01 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ Sw01 ∷ CZ23 ∷ CCZ123 ∷ Sw01 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ CS03⁻ ∷ CS23⁻ ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ K0 ∷ ι ∷ Sw01 ∷ CZ23 ∷ CCZ123 ∷ Sw01 ∷ CS01⁻ ∷ [])
  b21 = at 7 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 8 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 9 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 11 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 12 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b22 : Chain (Toff023 ∷ CS01 ∷ CS03⁻ ∷ CS23⁻ ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ K0 ∷ ι ∷ Sw01 ∷ CZ23 ∷ CCZ123 ∷ Sw01 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ CS03⁻ ∷ CS23⁻ ∷ Toff023 ∷ CZ23 ∷ CS23 ∷ Sw01 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ CS01⁻ ∷ [])
  b22 = at 11 2 (K1 ∷ Sw01 ∷ []) wn00123 ▸
       at 12 2 (ι1 ∷ Sw01 ∷ []) wn00124 ▸
       at 5 8 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) wn00125 ▸
       at 5 8 (Toff123 ∷ []) (by-assoc Eq.refl) ▸
       at 4 3 (Toff023 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CZ23 ∷ Sw01 ∷ []) (low-comm (Swap) (CZ)) ▸
       at 7 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸ done

  b23 : Chain (Toff023 ∷ CS01 ∷ CS03⁻ ∷ CS23⁻ ∷ Toff023 ∷ CZ23 ∷ CS23 ∷ Sw01 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ CS03⁻ ∷ CS23⁻ ∷ Toff023 ∷ CZ23 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ Sw01 ∷ CS01⁻ ∷ [])
  b23 = at 7 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 8 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 9 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 11 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 12 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b24 : Chain (Toff023 ∷ CS01 ∷ CS03⁻ ∷ CS23⁻ ∷ Toff023 ∷ CZ23 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ Sw01 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ CS03⁻ ∷ CS23⁻ ∷ Toff023 ∷ CZ23 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ CS12 ∷ Sw01 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ CS01⁻ ∷ [])
  b24 = at 6 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 7 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 8 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 9 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 10 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 12 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸ done

  b25 : Chain (Toff023 ∷ CS01 ∷ CS03⁻ ∷ CS23⁻ ∷ Toff023 ∷ CZ23 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ CS12 ∷ Sw01 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ CS03⁻ ∷ CS23⁻ ∷ Sw01 ∷ Toff123 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ [])
  b25 = at 13 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 11 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸
       at 7 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 6 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00031 ▸
       at 5 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 4 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸ done

  b26 : Chain (Toff023 ∷ CS01 ∷ CS03⁻ ∷ CS23⁻ ∷ Sw01 ∷ Toff123 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ CS03⁻ ∷ CS23⁻ ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ [])
  b26 = at 5 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 5 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 6 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 7 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 8 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b27 : Chain (Toff023 ∷ CS01 ∷ CS03⁻ ∷ CS23⁻ ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ CS03⁻ ∷ CS23⁻ ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ K1 ∷ ι1 ∷ Sw01 ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ [])
  b27 = at 10 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 11 2 (ι ∷ Sw01 ∷ []) wn00122 ▸
       at 12 2 [] wn00031 ▸
       at 11 2 (Sw01 ∷ ι1 ∷ []) wn00127 ▸
       at 10 2 (Sw01 ∷ K1 ∷ []) wn00118 ▸ done

  b28 : Chain (Toff023 ∷ CS01 ∷ CS03⁻ ∷ CS23⁻ ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ K1 ∷ ι1 ∷ Sw01 ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ CS03⁻ ∷ CS23⁻ ∷ K0 ∷ CS23 ∷ Sw01 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ [])
  b28 = at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 10 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 9 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 10 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸
       at 7 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 6 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸ done

  b29 : Chain (Toff023 ∷ CS01 ∷ CS03⁻ ∷ CS23⁻ ∷ K0 ∷ CS23 ∷ Sw01 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ CS03⁻ ∷ K0 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ CS23⁻ ∷ Sw01 ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ [])
  b29 = at 5 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 4 2 (Sw01 ∷ K1 ∷ []) wn00118 ▸
       at 5 8 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) wn00125 ▸
       at 5 8 (Toff123 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 4 2 (Toff123 ∷ CS23⁻ ∷ []) wn01472 ▸
       at 4 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸ done

  b30 : Chain (Toff023 ∷ CS01 ∷ CS03⁻ ∷ K0 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ CS23⁻ ∷ Sw01 ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ CS03⁻ ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ K1 ∷ ι1 ∷ CS23⁻ ∷ Sw01 ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ [])
  b30 = at 4 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 5 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 6 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 7 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b31 : Chain (Toff023 ∷ CS01 ∷ CS03⁻ ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ K1 ∷ ι1 ∷ CS23⁻ ∷ Sw01 ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ CS03⁻ ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ Sw01 ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ Sw01 ∷ CS23⁻ ∷ Sw01 ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ [])
  b31 = at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 10 2 (ι ∷ Sw01 ∷ []) wn00122 ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 4 2 (K1 ∷ Sw01 ∷ []) wn00123 ▸
       at 5 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 6 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 7 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸ done

  b32 : Chain (Toff023 ∷ CS01 ∷ CS03⁻ ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ Sw01 ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ Sw01 ∷ CS23⁻ ∷ Sw01 ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ CS03⁻ ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ CS23⁻ ∷ Sw01 ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ [])
  b32 = at 8 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (K1 ∷ Sw01 ∷ []) wn00123 ▸
       at 11 2 (ι1 ∷ Sw01 ∷ []) wn00124 ▸ done

  b33 : Chain (Toff023 ∷ CS01 ∷ CS03⁻ ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ CS23⁻ ∷ Sw01 ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ CS03⁻ ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CS23⁻ ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ [])
  b33 = at 4 8 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) wn00125 ▸
       at 4 8 (Toff123 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (Toff023 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 5 2 [] wn00031 ▸
       at 4 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 3 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸ done

  b34 : Chain (Toff023 ∷ CS01 ∷ CS03⁻ ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CS23⁻ ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ CS03⁻ ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CS23⁻ ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ [])
  b34 = at 3 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 4 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 5 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 6 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 7 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸ done

  b35 : Chain (Toff023 ∷ CS01 ∷ CS03⁻ ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CS23⁻ ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ CS03⁻ ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ K1 ∷ ι1 ∷ Sw01 ∷ CS23⁻ ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ [])
  b35 = at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 10 2 (ι ∷ Sw01 ∷ []) wn00122 ▸
       at 11 2 [] wn00031 ▸
       at 10 2 (Sw01 ∷ ι1 ∷ []) wn00127 ▸
       at 9 2 (Sw01 ∷ K1 ∷ []) wn00118 ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b36 : Chain (Toff023 ∷ CS01 ∷ CS03⁻ ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ K1 ∷ ι1 ∷ Sw01 ∷ CS23⁻ ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ CS03⁻ ∷ K0 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ CS23⁻ ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ [])
  b36 = at 10 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 9 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 8 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 9 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸
       at 6 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 5 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸
       at 4 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸ done

  b37 : Chain (Toff023 ∷ CS01 ∷ CS03⁻ ∷ K0 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ CS23⁻ ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ Sw01 ∷ CS13⁻ ∷ Toff123 ∷ Sw01 ∷ CS23⁻ ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ [])
  b37 = at 3 2 (Sw01 ∷ K1 ∷ []) wn00118 ▸
       at 4 8 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) wn00125 ▸
       at 4 8 (Toff123 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 3 2 (Sw01 ∷ CS12⁻ ∷ []) wn00076 ▸
       at 2 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 3 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b38 : Chain (Toff023 ∷ CS01 ∷ Sw01 ∷ CS13⁻ ∷ Toff123 ∷ Sw01 ∷ CS23⁻ ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ K1 ∷ ι1 ∷ CS13⁻ ∷ CS23⁻ ∷ CCZ123 ∷ Sw01 ∷ CS23⁻ ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ [])
  b38 = at 3 2 (Toff123 ∷ CS13⁻ ∷ CS23⁻ ∷ CCZ123 ∷ []) wn01471 ▸
       at 3 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 3 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 4 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 5 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 6 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b39 : Chain (Toff023 ∷ CS01 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ K1 ∷ ι1 ∷ CS13⁻ ∷ CS23⁻ ∷ CCZ123 ∷ Sw01 ∷ CS23⁻ ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ Sw01 ∷ K1 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ Sw01 ∷ CS13⁻ ∷ CS23⁻ ∷ CCZ123 ∷ Sw01 ∷ CS23⁻ ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ [])
  b39 = at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 9 2 (ι ∷ Sw01 ∷ []) wn00122 ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 3 2 (K1 ∷ Sw01 ∷ []) wn00123 ▸ done

  b40 : Chain (Toff023 ∷ CS01 ∷ Sw01 ∷ K1 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ Sw01 ∷ CS13⁻ ∷ CS23⁻ ∷ CCZ123 ∷ Sw01 ∷ CS23⁻ ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ K0 ∷ ι ∷ Sw01 ∷ CS13⁻ ∷ CS23⁻ ∷ CCZ123 ∷ Sw01 ∷ CS23⁻ ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ [])
  b40 = at 4 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 5 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 6 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 7 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b41 : Chain (Toff023 ∷ CS01 ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ K0 ∷ ι ∷ Sw01 ∷ CS13⁻ ∷ CS23⁻ ∷ CCZ123 ∷ Sw01 ∷ CS23⁻ ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ Toff023 ∷ Sw23 ∷ Sw01 ∷ CS12⁻ ∷ Sw23 ∷ CS23⁻ ∷ CCZ123 ∷ Sw01 ∷ CS23⁻ ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ [])
  b41 = at 8 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K1 ∷ Sw01 ∷ []) wn00123 ▸
       at 10 2 (ι1 ∷ Sw01 ∷ []) wn00124 ▸
       at 3 8 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) wn00125 ▸
       at 3 8 (Toff123 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff023 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b42 : Chain (Toff023 ∷ CS01 ∷ Toff023 ∷ Sw23 ∷ Sw01 ∷ CS12⁻ ∷ Sw23 ∷ CS23⁻ ∷ CCZ123 ∷ Sw01 ∷ CS23⁻ ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ Toff023 ∷ CS03⁻ ∷ CS23⁻ ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ CS13 ∷ Sw01 ∷ CS23⁻ ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ [])
  b42 = at 4 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 3 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 6 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 6 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 7 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸ done

  b43 : Chain (Toff023 ∷ CS01 ∷ Toff023 ∷ CS03⁻ ∷ CS23⁻ ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ CS13 ∷ Sw01 ∷ CS23⁻ ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ Toff023 ∷ CS03⁻ ∷ CS23⁻ ∷ Sw01 ∷ CS23 ∷ Sw01 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ Sw01 ∷ CS23⁻ ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ [])
  b43 = at 8 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 6 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸ done

  b44 : Chain (Toff023 ∷ CS01 ∷ Toff023 ∷ CS03⁻ ∷ CS23⁻ ∷ Sw01 ∷ CS23 ∷ Sw01 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ Sw01 ∷ CS23⁻ ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ Toff023 ∷ CS03⁻ ∷ CS23⁻ ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CS23⁻ ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ [])
  b44 = at 7 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 8 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 9 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 11 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 12 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b45 : Chain (Toff023 ∷ CS01 ∷ Toff023 ∷ CS03⁻ ∷ CS23⁻ ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CS23⁻ ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ Toff023 ∷ CS03⁻ ∷ CCZ023 ∷ CCZ023 ∷ Sw01 ∷ Sw01 ∷ CS01⁻ ∷ [])
  b45 = at 6 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸
       at 6 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00031 ▸
       at 5 2 (CS23⁻ ∷ CCZ023 ∷ []) (lem-pass-CCZ023-vs-CSd23) ▸
       at 6 2 (CZ23 ∷ CCZ023 ∷ []) (lem-pass-CCZ023-vs-CZ23) ▸
       at 4 3 [] wn01473 ▸
       at 6 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸ done

  b46 : Chain (Toff023 ∷ CS01 ∷ Toff023 ∷ CS03⁻ ∷ CCZ023 ∷ CCZ023 ∷ Sw01 ∷ Sw01 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ Toff023 ∷ CS03⁻ ∷ CCZ023 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CS01⁻ ∷ [])
  b46 = at 5 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 6 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 7 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 8 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b47 : Chain (Toff023 ∷ CS01 ∷ Toff023 ∷ CS03⁻ ∷ CCZ023 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ Toff023 ∷ CS03⁻ ∷ CCZ023 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ CS01⁻ ∷ [])
  b47 = at 10 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00031 ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 10 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 9 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b48 : Chain (Toff023 ∷ CS01 ∷ Toff023 ∷ CS03⁻ ∷ CCZ023 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ Toff023 ∷ CS03⁻ ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ CS01⁻ ∷ [])
  b48 = at 10 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸
       at 7 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 6 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸
       at 5 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 6 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸
       at 6 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸ done

  b49 : Chain (Toff023 ∷ CS01 ∷ Toff023 ∷ CS03⁻ ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ Toff023 ∷ CS03⁻ ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ CS01⁻ ∷ [])
  b49 = at 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 5 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 6 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 7 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸ done

  b50 : Chain (Toff023 ∷ CS01 ∷ Toff023 ∷ CS03⁻ ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ Toff023 ∷ CS03⁻ ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ CCZ123 ∷ Sw01 ∷ CS01⁻ ∷ [])
  b50 = at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00031 ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 9 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 8 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 9 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b51 : Chain (Toff023 ∷ CS01 ∷ Toff023 ∷ CS03⁻ ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ CCZ123 ∷ Sw01 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ Toff023 ∷ CS03⁻ ∷ CS01⁻ ∷ [])
  b51 = at 7 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸
       at 6 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 5 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸
       at 4 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 5 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸
       at 5 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00033 ▸
       at 4 2 [] wn00031 ▸ done

  b52 : Chain (Toff023 ∷ CS01 ∷ Toff023 ∷ CS03⁻ ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ CS03⁻ ∷ [])
  b52 = at 3 2 (CS01⁻ ∷ CS03⁻ ∷ []) (lem-pass-CSd03-vs-CSd01) ▸ done

-- pass [X3 CKd30 X3] [CS03 TOFF012 CSd03 TOFF012]: 33 steps
lem-pass-X3-CKd30-X3-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (X3 ∷ CK30⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd30-X3-vs-CS03-TOFF012-CSd03-TOFF012 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (run b4))))
  where
  b0 : Chain (X3 ∷ CK30⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK30⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 0 (CS02 ∷ CS02⁻ ∷ []) wn01357 ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 0 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸
       at 1 0 (Toff012 ∷ Toff012 ∷ []) wn00045 ▸ done

  b1 : Chain (CS03 ∷ Toff012 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK30⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK30⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ [])
  b1 = at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 0 (CS02⁻ ∷ CS02 ∷ []) wn00231 ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸
       at 3 0 (Toff012 ∷ Toff012 ∷ []) wn00045 ▸ done

  b2 : Chain (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK30⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ [])
  b2 = at 4 7 (X3 ∷ CK30⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (sym lem-pass-X3-CKd30-X3-vs-TOFF012-CS03-TOFF012-CSd03) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 [] wn00003 ▸
       at 10 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] wn00003 ▸
       at 11 2 [] wn01358 ▸
       at 10 2 [] wn00003 ▸ done

  b3 : Chain (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ Toff012 ∷ Toff012 ∷ [])
  b3 = at 9 2 [] wn00227 ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 9 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] wn00003 ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00003 ▸
       at 9 2 [] wn01342 ▸
       at 8 2 [] wn00003 ▸ done

  b4 : Chain (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ Toff012 ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ [])
  b4 = at 7 2 [] wn00227 ▸ done

-- pass [X2 CSd20 X2] [CS03 TOFF012 CSd03 TOFF012]: 33 steps
lem-pass-X2-CSd20-X2-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (X2 ∷ CS02⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CSd20-X2-vs-CS03-TOFF012-CSd03-TOFF012 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (run b4))))
  where
  b0 : Chain (X2 ∷ CS02⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ CS02⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 0 (CS02 ∷ CS02⁻ ∷ []) wn01357 ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 0 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸
       at 1 0 (Toff012 ∷ Toff012 ∷ []) wn00045 ▸ done

  b1 : Chain (CS03 ∷ Toff012 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ CS02⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ CS02⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ [])
  b1 = at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 0 (CS02⁻ ∷ CS02 ∷ []) wn00231 ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸
       at 3 0 (Toff012 ∷ Toff012 ∷ []) wn00045 ▸ done

  b2 : Chain (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ CS02⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ [])
  b2 = at 4 7 (X2 ∷ CS02⁻ ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (sym lem-pass-X2-CSd20-X2-vs-TOFF012-CS03-TOFF012-CSd03) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 [] wn00003 ▸
       at 10 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] wn00003 ▸
       at 11 2 [] wn01358 ▸
       at 10 2 [] wn00003 ▸ done

  b3 : Chain (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ Toff012 ∷ Toff012 ∷ [])
  b3 = at 9 2 [] wn00227 ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 9 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] wn00003 ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00003 ▸
       at 9 2 [] wn01342 ▸
       at 8 2 [] wn00003 ▸ done

  b4 : Chain (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ Toff012 ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ [])
  b4 = at 7 2 [] wn00227 ▸ done

-- pass [CS21] [X2 CS03 TOFF012 CSd03 TOFF012 X2]: 3 steps
lem-pass-CS21-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 : ⟪ (CS12 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CS12 ∷ []) ⟫ʷ
lem-pass-CS21-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 = run b0
  where
  b0 : Chain (CS12 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CS12 ∷ [])
  b0 = at 0 2 (X2 ∷ X2 ∷ CS12 ∷ X2 ∷ []) wn01474 ▸
       at 1 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (lem-pass-X2-CS21-X2-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 5 4 (X2 ∷ CS12 ∷ []) wn01475 ▸ done

-- pass [CK21] [X2 CS03 TOFF012 CSd03 TOFF012 X2]: 3 steps
lem-pass-CK21-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 : ⟪ (CK21 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CK21 ∷ []) ⟫ʷ
lem-pass-CK21-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 = run b0
  where
  b0 : Chain (CK21 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CK21 ∷ [])
  b0 = at 0 2 (X2 ∷ X2 ∷ CK21 ∷ X2 ∷ []) wn01476 ▸
       at 1 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CK21 ∷ X2 ∷ []) (lem-pass-X2-CK21-X2-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 5 4 (X2 ∷ CK21 ∷ []) wn01477 ▸ done

-- pass [CKd21] [X2 CS03 TOFF012 CSd03 TOFF012 X2]: 3 steps
lem-pass-CKd21-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 : ⟪ (CK21⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CK21⁻ ∷ []) ⟫ʷ
lem-pass-CKd21-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 = run b0
  where
  b0 : Chain (CK21⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CK21⁻ ∷ [])
  b0 = at 0 2 (X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) wn01478 ▸
       at 1 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd21-X2-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 5 4 (X2 ∷ CK21⁻ ∷ []) wn01479 ▸ done

-- pass [CSd21] [X2 CS03 TOFF012 CSd03 TOFF012 X2]: 3 steps
lem-pass-CSd21-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 : ⟪ (CS12⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CS12⁻ ∷ []) ⟫ʷ
lem-pass-CSd21-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 = run b0
  where
  b0 : Chain (CS12⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CS12⁻ ∷ [])
  b0 = at 0 2 (X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) wn01480 ▸
       at 1 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd21-X2-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 5 4 (X2 ∷ CS12⁻ ∷ []) wn01481 ▸ done

-- pass [X2 CSd20 X2] [S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1]: 5 steps
lem-pass-X2-CSd20-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 : ⟪ (X2 ∷ CS02⁻ ∷ X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CSd20-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 = run b0
  where
  b0 : Chain (X2 ∷ CS02⁻ ∷ X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ CS02⁻ ∷ X2 ∷ [])
  b0 = at 0 3 (X2 ∷ CS02⁻ ∷ X2 ∷ []) wn01482 ▸
       at 0 5 (S1 ∷ K1 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) wn01483 ▸
       at 2 7 (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd20-X2-vs-TOFF102-CS13-TOFF102-CSd13) ▸
       at 6 5 (K1⁻ ∷ S1⁻ ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) wn01484 ▸
       at 8 3 (X2 ∷ CS02⁻ ∷ X2 ∷ []) wn01482 ▸ done

-- pass [X2 CKd20 X2] [S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1]: 5 steps
lem-pass-X2-CKd20-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 : ⟪ (X2 ∷ CK20⁻ ∷ X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CKd20-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 = run b0
  where
  b0 : Chain (X2 ∷ CK20⁻ ∷ X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ CK20⁻ ∷ X2 ∷ [])
  b0 = at 0 3 (X2 ∷ CK20⁻ ∷ X2 ∷ []) wn01485 ▸
       at 0 5 (S1 ∷ K1 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) wn01486 ▸
       at 2 7 (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd20-X2-vs-TOFF102-CS13-TOFF102-CSd13) ▸
       at 6 5 (K1⁻ ∷ S1⁻ ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) wn01487 ▸
       at 8 3 (X2 ∷ CK20⁻ ∷ X2 ∷ []) wn01485 ▸ done

-- pass [X2 CK20 X2] [S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1]: 5 steps
lem-pass-X2-CK20-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 : ⟪ (X2 ∷ CK20 ∷ X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CK20-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 = run b0
  where
  b0 : Chain (X2 ∷ CK20 ∷ X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ [])
  b0 = at 0 3 (X2 ∷ CK20 ∷ X2 ∷ []) wn01413 ▸
       at 0 5 (S1 ∷ K1 ∷ X2 ∷ CK20 ∷ X2 ∷ []) wn01488 ▸
       at 2 7 (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ []) (lem-pass-X2-CK20-X2-vs-TOFF102-CS13-TOFF102-CSd13) ▸
       at 6 5 (K1⁻ ∷ S1⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ []) wn01489 ▸
       at 8 3 (X2 ∷ CK20 ∷ X2 ∷ []) wn01413 ▸ done

-- pass [X2 CS20 X2] [S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1]: 5 steps
lem-pass-X2-CS20-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 : ⟪ (X2 ∷ CS02 ∷ X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ CS02 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CS20-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 = run b0
  where
  b0 : Chain (X2 ∷ CS02 ∷ X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ CS02 ∷ X2 ∷ [])
  b0 = at 0 3 (X2 ∷ CS02 ∷ X2 ∷ []) wn01490 ▸
       at 0 5 (S1 ∷ K1 ∷ X2 ∷ CS02 ∷ X2 ∷ []) wn01491 ▸
       at 2 7 (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS02 ∷ X2 ∷ []) (lem-pass-X2-CS20-X2-vs-TOFF102-CS13-TOFF102-CSd13) ▸
       at 6 5 (K1⁻ ∷ S1⁻ ∷ X2 ∷ CS02 ∷ X2 ∷ []) wn01492 ▸
       at 8 3 (X2 ∷ CS02 ∷ X2 ∷ []) wn01490 ▸ done

-- pass [X2 CS21 X2] [X3 CS03 TOFF012 CSd03 TOFF012 X3]: 5 steps
lem-pass-X2-CS21-X2-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : ⟪ (X2 ∷ CS12 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CS21-X2-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = run b0
  where
  b0 : Chain (X2 ∷ CS12 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ X2 ∷ CS12 ∷ X2 ∷ [])
  b0 = at 0 4 (X3 ∷ X2 ∷ CS12 ∷ X2 ∷ []) wn01493 ▸
       at 1 3 (X2 ∷ CS12 ∷ X2 ∷ []) wn01494 ▸
       at 1 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (lem-pass-X2-CS21-X2-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 5 3 (X2 ∷ CS12 ∷ X2 ∷ []) wn01494 ▸
       at 5 4 (X3 ∷ X2 ∷ CS12 ∷ X2 ∷ []) wn01493 ▸ done

-- pass [X2 CK21 X2] [X3 CS03 TOFF012 CSd03 TOFF012 X3]: 5 steps
lem-pass-X2-CK21-X2-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : ⟪ (X2 ∷ CK21 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CK21-X2-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = run b0
  where
  b0 : Chain (X2 ∷ CK21 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ [])
  b0 = at 0 4 (X3 ∷ X2 ∷ CK21 ∷ X2 ∷ []) wn01495 ▸
       at 1 3 (X2 ∷ CK21 ∷ X2 ∷ []) wn01496 ▸
       at 1 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CK21 ∷ X2 ∷ []) (lem-pass-X2-CK21-X2-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 5 3 (X2 ∷ CK21 ∷ X2 ∷ []) wn01496 ▸
       at 5 4 (X3 ∷ X2 ∷ CK21 ∷ X2 ∷ []) wn01495 ▸ done

-- pass [X2 CKd21 X2] [X3 CS03 TOFF012 CSd03 TOFF012 X3]: 5 steps
lem-pass-X2-CKd21-X2-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : ⟪ (X2 ∷ CK21⁻ ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CKd21-X2-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = run b0
  where
  b0 : Chain (X2 ∷ CK21⁻ ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ [])
  b0 = at 0 4 (X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) wn01497 ▸
       at 1 3 (X2 ∷ CK21⁻ ∷ X2 ∷ []) wn01498 ▸
       at 1 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd21-X2-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 5 3 (X2 ∷ CK21⁻ ∷ X2 ∷ []) wn01498 ▸
       at 5 4 (X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) wn01497 ▸ done

-- pass [X2 CSd21 X2] [X3 CS03 TOFF012 CSd03 TOFF012 X3]: 5 steps
lem-pass-X2-CSd21-X2-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CSd21-X2-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = run b0
  where
  b0 : Chain (X2 ∷ CS12⁻ ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ [])
  b0 = at 0 4 (X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) wn01499 ▸
       at 1 3 (X2 ∷ CS12⁻ ∷ X2 ∷ []) wn01500 ▸
       at 1 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd21-X2-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 5 3 (X2 ∷ CS12⁻ ∷ X2 ∷ []) wn01500 ▸
       at 5 4 (X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) wn01499 ▸ done

-- pass [TOFF102 CS13 TOFF102 CSd13] [S0]: 1 steps
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-S0 : ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-S0 = run b0
  where
  b0 : Chain (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ S0 ∷ []) (S0 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  b0 = at 0 5 (S0 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (sym lem-pass-S0-vs-TOFF102-CS13-TOFF102-CSd13) ▸ done

-- pass [TOFF103 CS12 TOFF103 CSd12] [S0]: 1 steps
lem-pass-TOFF103-CS12-TOFF103-CSd12-vs-S0 : ⟪ (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) ⟫ʷ
lem-pass-TOFF103-CS12-TOFF103-CSd12-vs-S0 = run b0
  where
  b0 : Chain (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ S0 ∷ []) (S0 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b0 = at 0 5 (S0 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (sym lem-pass-S0-vs-TOFF103-CS12-TOFF103-CSd12) ▸ done

-- pass [TOFF103 CS12 TOFF103 CSd12] [CSd03]: 1 steps
lem-pass-TOFF103-CS12-TOFF103-CSd12-vs-CSd03 : ⟪ (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) ⟫ʷ
lem-pass-TOFF103-CS12-TOFF103-CSd12-vs-CSd03 = run b0
  where
  b0 : Chain (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b0 = at 0 5 (CS03⁻ ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (sym lem-pass-CSd03-vs-TOFF103-CS12-TOFF103-CSd12) ▸ done

-- pass [TOFF123] [CSd03]: 21 steps
lem-pass-TOFF123-vs-CSd03 : ⟪ (Toff123 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ Toff123 ∷ []) ⟫ʷ
lem-pass-TOFF123-vs-CSd03 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Toff123 ∷ CS03⁻ ∷ []) (K1 ∷ CCZ123 ∷ CS03⁻ ∷ Sw23 ∷ K1⁻ ∷ Sw23 ∷ [])
  b0 = at 0 1 (K1 ∷ CCZ123 ∷ K1⁻ ∷ []) wn00128 ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 2 2 (Sw23 ∷ K1⁻ ∷ []) (low-comm (((K • iI) ↑)) (Swap)) ▸
       at 3 2 (CS02⁻ ∷ K1⁻ ∷ []) wn01448 ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (K1 ∷ CCZ123 ∷ CS03⁻ ∷ Sw23 ∷ K1⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS02⁻ ∷ K1 ∷ Sw23 ∷ CCZ123 ∷ K1⁻ ∷ [])
  b1 = at 3 2 (K1⁻ ∷ Sw23 ∷ []) (sym (low-comm (((K • iI) ↑)) (Swap))) ▸
       at 4 2 [] wn00003 ▸
       at 1 2 (CS03⁻ ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-CSd03) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸
       at 0 2 (Sw23 ∷ K1 ∷ []) (low-comm ((K ↑)) (Swap)) ▸
       at 1 2 (CS02⁻ ∷ K1 ∷ []) wn01449 ▸ done

  b2 : Chain (Sw23 ∷ CS02⁻ ∷ K1 ∷ Sw23 ∷ CCZ123 ∷ K1⁻ ∷ []) (CS03⁻ ∷ Toff123 ∷ [])
  b2 = at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 0 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 2 2 [] wn00003 ▸
       at 1 3 (Toff123 ∷ []) wn01437 ▸ done

-- pass [TOFF123 CS01 TOFF123 CSd01] [S0]: 1 steps
lem-pass-TOFF123-CS01-TOFF123-CSd01-vs-S0 : ⟪ (Toff123 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ Toff123 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ []) ⟫ʷ
lem-pass-TOFF123-CS01-TOFF123-CSd01-vs-S0 = run b0
  where
  b0 : Chain (Toff123 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ S0 ∷ []) (S0 ∷ Toff123 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ [])
  b0 = at 0 5 (S0 ∷ Toff123 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ []) (sym lem-pass-S0-vs-TOFF123-CS01-TOFF123-CSd01) ▸ done

-- pass [CS21] [X2 TOFF102 CS13 TOFF102 CSd13 X2]: 3 steps
lem-pass-CS21-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 : ⟪ (CS12 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS12 ∷ []) ⟫ʷ
lem-pass-CS21-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 = run b0
  where
  b0 : Chain (CS12 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ []) (X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS12 ∷ [])
  b0 = at 0 2 (X2 ∷ X2 ∷ CS12 ∷ X2 ∷ []) wn01474 ▸
       at 1 7 (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS12 ∷ X2 ∷ []) (lem-pass-X2-CS21-X2-vs-TOFF102-CS13-TOFF102-CSd13) ▸
       at 5 4 (X2 ∷ CS12 ∷ []) wn01475 ▸ done

-- pass [X2 CSd21 X2] [S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0]: 5 steps
lem-pass-X2-CSd21-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CSd21-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = run b0
  where
  b0 : Chain (X2 ∷ CS12⁻ ∷ X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ CS12⁻ ∷ X2 ∷ [])
  b0 = at 0 3 (X2 ∷ CS12⁻ ∷ X2 ∷ []) wn01500 ▸
       at 0 5 (S0 ∷ K0 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) wn01501 ▸
       at 2 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd21-X2-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 6 5 (K0⁻ ∷ S0⁻ ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) wn01502 ▸
       at 8 3 (X2 ∷ CS12⁻ ∷ X2 ∷ []) wn01500 ▸ done

-- pass [X2 CKd21 X2] [S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0]: 5 steps
lem-pass-X2-CKd21-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : ⟪ (X2 ∷ CK21⁻ ∷ X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CKd21-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = run b0
  where
  b0 : Chain (X2 ∷ CK21⁻ ∷ X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ CK21⁻ ∷ X2 ∷ [])
  b0 = at 0 3 (X2 ∷ CK21⁻ ∷ X2 ∷ []) wn01498 ▸
       at 0 5 (S0 ∷ K0 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) wn01503 ▸
       at 2 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd21-X2-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 6 5 (K0⁻ ∷ S0⁻ ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) wn01504 ▸
       at 8 3 (X2 ∷ CK21⁻ ∷ X2 ∷ []) wn01498 ▸ done

-- pass [X2 CK21 X2] [S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0]: 5 steps
lem-pass-X2-CK21-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : ⟪ (X2 ∷ CK21 ∷ X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ CK21 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CK21-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = run b0
  where
  b0 : Chain (X2 ∷ CK21 ∷ X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ CK21 ∷ X2 ∷ [])
  b0 = at 0 3 (X2 ∷ CK21 ∷ X2 ∷ []) wn01496 ▸
       at 0 5 (S0 ∷ K0 ∷ X2 ∷ CK21 ∷ X2 ∷ []) wn01505 ▸
       at 2 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CK21 ∷ X2 ∷ []) (lem-pass-X2-CK21-X2-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 6 5 (K0⁻ ∷ S0⁻ ∷ X2 ∷ CK21 ∷ X2 ∷ []) wn01506 ▸
       at 8 3 (X2 ∷ CK21 ∷ X2 ∷ []) wn01496 ▸ done

-- pass [X2 CS21 X2] [S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0]: 5 steps
lem-pass-X2-CS21-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : ⟪ (X2 ∷ CS12 ∷ X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CS21-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = run b0
  where
  b0 : Chain (X2 ∷ CS12 ∷ X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ CS12 ∷ X2 ∷ [])
  b0 = at 0 3 (X2 ∷ CS12 ∷ X2 ∷ []) wn01494 ▸
       at 0 5 (S0 ∷ K0 ∷ X2 ∷ CS12 ∷ X2 ∷ []) wn01507 ▸
       at 2 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (lem-pass-X2-CS21-X2-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 6 5 (K0⁻ ∷ S0⁻ ∷ X2 ∷ CS12 ∷ X2 ∷ []) wn01508 ▸
       at 8 3 (X2 ∷ CS12 ∷ X2 ∷ []) wn01494 ▸ done

-- pass [X2 CS21 X2] [X3 TOFF102 CS13 TOFF102 CSd13 X3]: 5 steps
lem-pass-X2-CS21-X2-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 : ⟪ (X2 ∷ CS12 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CS21-X2-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 = run b0
  where
  b0 : Chain (X2 ∷ CS12 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ []) (X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ X2 ∷ CS12 ∷ X2 ∷ [])
  b0 = at 0 4 (X3 ∷ X2 ∷ CS12 ∷ X2 ∷ []) wn01493 ▸
       at 1 3 (X2 ∷ CS12 ∷ X2 ∷ []) wn01494 ▸
       at 1 7 (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS12 ∷ X2 ∷ []) (lem-pass-X2-CS21-X2-vs-TOFF102-CS13-TOFF102-CSd13) ▸
       at 5 3 (X2 ∷ CS12 ∷ X2 ∷ []) wn01494 ▸
       at 5 4 (X3 ∷ X2 ∷ CS12 ∷ X2 ∷ []) wn01493 ▸ done

-- pass [X2 CS20 X2] [X3 TOFF102 CS13 TOFF102 CSd13 X3]: 25 steps
lem-pass-X2-CS20-X2-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 : ⟪ (X2 ∷ CS02 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ X2 ∷ CS02 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CS20-X2-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (X2 ∷ CS02 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ []) (X3 ∷ X2 ∷ Sw01 ∷ CS12 ∷ X2 ∷ Sw01 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ [])
  b0 = at 4 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 3 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸
       at 2 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 1 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 0 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 1 4 (X3 ∷ X2 ∷ CS12 ∷ X2 ∷ []) wn01493 ▸
       at 0 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸
       at 1 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸ done

  b1 : Chain (X3 ∷ X2 ∷ Sw01 ∷ CS12 ∷ X2 ∷ Sw01 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ []) (X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS02 ∷ X2 ∷ Sw01 ∷ X3 ∷ Sw01 ∷ [])
  b1 = at 2 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 3 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 4 2 [] wn00031 ▸
       at 1 3 (X2 ∷ CS02 ∷ X2 ∷ []) wn01490 ▸
       at 1 7 (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS02 ∷ X2 ∷ []) (lem-pass-X2-CS20-X2-vs-TOFF102-CS13-TOFF102-CSd13) ▸
       at 5 3 (X2 ∷ CS02 ∷ X2 ∷ []) wn01490 ▸
       at 9 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 8 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸ done

  b2 : Chain (X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS02 ∷ X2 ∷ Sw01 ∷ X3 ∷ Sw01 ∷ []) (X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ X2 ∷ CS02 ∷ X2 ∷ Sw01 ∷ Sw01 ∷ [])
  b2 = at 7 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 6 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 5 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 6 4 (X3 ∷ X2 ∷ CS12 ∷ X2 ∷ []) wn01493 ▸
       at 5 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸
       at 6 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 7 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 8 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸ done

  b3 : Chain (X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ X2 ∷ CS02 ∷ X2 ∷ Sw01 ∷ Sw01 ∷ []) (X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ X2 ∷ CS02 ∷ X2 ∷ [])
  b3 = at 9 2 [] wn00031 ▸ done

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D540 where

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
open import Examples.Groups.Clifford+CS.Four.Wins.W01 using (wn00005 ; wn00007 ; wn00024 ; wn00025 ; wn00026 ; wn00027 ; wn00030 ; wn00031 ; wn00033 ; wn00074 ; wn00118 ; wn00121 ; wn00122 ; wn00123 ; wn00124 ; wn00125 ; wn00127)
open import Examples.Groups.Clifford+CS.Four.Wins.W02 using (wn00315)
open import Examples.Groups.Clifford+CS.Four.Wins.W03 using (wn00481)
open import Examples.Groups.Clifford+CS.Four.Wins.W27 using (wn01374)
open import Examples.Groups.Clifford+CS.Four.Wins.W28 using (wn01468 ; wn01469 ; wn01470)
open import Examples.Groups.Clifford+CS.Four.D.D013 using (lem-pass-CCZ023-vs-CS23 ; lem-pass-CCZ023-vs-CZ23 ; lem-pass-CS23-vs-CS01 ; lem-pass-S0-vs-CS01 ; lem-pass-S0-vs-CSd01)
open import Examples.Groups.Clifford+CS.Four.D.D513 using (lem-pass-CCZ023-vs-CS01)

-- pass [S0] [TOFF023 CS01 TOFF023 CSd01]: 401 steps
lem-pass-S0-vs-TOFF023-CS01-TOFF023-CSd01 : ⟪ (S0 ∷ Toff023 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ S0 ∷ []) ⟫ʷ
lem-pass-S0-vs-TOFF023-CS01-TOFF023-CSd01 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (trans (run b38) (trans (run b39) (trans (run b40) (trans (run b41) (trans (run b42) (trans (run b43) (trans (run b44) (trans (run b45) (trans (run b46) (trans (run b47) (trans (run b48) (trans (run b49) (run b50))))))))))))))))))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (S0 ∷ Toff023 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ []) (S0 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ [])
  b0 = at 2 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 1 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 2 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 3 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 4 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 5 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸ done

  b1 : Chain (S0 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ []) (S0 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ Sw01 ∷ Sw01 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ [])
  b1 = at 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 8 2 (ι ∷ Sw01 ∷ []) wn00122 ▸
       at 9 2 [] wn00031 ▸ done

  b2 : Chain (S0 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ Sw01 ∷ Sw01 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ []) (S0 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ [])
  b2 = at 8 2 (Sw01 ∷ ι1 ∷ []) wn00127 ▸
       at 7 2 (Sw01 ∷ K1 ∷ []) wn00118 ▸
       at 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 7 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 6 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 7 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸ done

  b3 : Chain (S0 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ []) (Sw01 ∷ Toff123 ∷ S1 ∷ CS23 ∷ CCZ123 ∷ Sw01 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ [])
  b3 = at 4 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 3 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸
       at 2 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 1 2 (Sw01 ∷ K1 ∷ []) wn00118 ▸
       at 2 8 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) wn00125 ▸
       at 2 8 (Toff123 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw01 ∷ S1 ∷ []) wn00481 ▸
       at 1 2 (Toff123 ∷ S1 ∷ CS23 ∷ CCZ123 ∷ []) wn01468 ▸ done

  b4 : Chain (Sw01 ∷ Toff123 ∷ S1 ∷ CS23 ∷ CCZ123 ∷ Sw01 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ []) (K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ K1 ∷ ι1 ∷ S1 ∷ CS23 ∷ CCZ123 ∷ Sw01 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ [])
  b4 = at 1 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 1 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 2 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 3 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 4 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b5 : Chain (K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ K1 ∷ ι1 ∷ S1 ∷ CS23 ∷ CCZ123 ∷ Sw01 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ []) (Sw01 ∷ K1 ∷ CS23 ∷ Sw01 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ Sw01 ∷ S1 ∷ CS23 ∷ CCZ123 ∷ Sw01 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ [])
  b5 = at 6 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 7 2 (ι ∷ Sw01 ∷ []) wn00122 ▸
       at 0 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 1 2 (K1 ∷ Sw01 ∷ []) wn00123 ▸
       at 2 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸ done

  b6 : Chain (Sw01 ∷ K1 ∷ CS23 ∷ Sw01 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ Sw01 ∷ S1 ∷ CS23 ∷ CCZ123 ∷ Sw01 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ []) (Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ K0 ∷ ι ∷ Sw01 ∷ S1 ∷ CS23 ∷ CCZ123 ∷ Sw01 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ [])
  b6 = at 3 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 4 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 5 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b7 : Chain (Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ K0 ∷ ι ∷ Sw01 ∷ S1 ∷ CS23 ∷ CCZ123 ∷ Sw01 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ []) (Toff023 ∷ S0 ∷ CS23 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ [])
  b7 = at 7 2 (K1 ∷ Sw01 ∷ []) wn00123 ▸
       at 8 2 (ι1 ∷ Sw01 ∷ []) wn00124 ▸
       at 1 8 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) wn00125 ▸
       at 1 8 (Toff123 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff023 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (S0 ∷ Sw01 ∷ []) wn00315 ▸
       at 2 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b8 : Chain (Toff023 ∷ S0 ∷ CS23 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ []) (Toff023 ∷ S0 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ [])
  b8 = at 3 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 4 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 5 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 6 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b9 : Chain (Toff023 ∷ S0 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ []) (Toff023 ∷ S0 ∷ CS23 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ Sw01 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ [])
  b9 = at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 4 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 5 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 6 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 7 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b10 : Chain (Toff023 ∷ S0 ∷ CS23 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ Sw01 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ []) (Toff023 ∷ S0 ∷ CS23 ∷ CS01 ∷ CCZ023 ∷ Toff023 ∷ CS01⁻ ∷ [])
  b10 = at 9 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸
       at 4 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00031 ▸
       at 3 2 (CS01 ∷ CCZ023 ∷ []) (lem-pass-CCZ023-vs-CS01) ▸ done

  b11 : Chain (Toff023 ∷ S0 ∷ CS23 ∷ CS01 ∷ CCZ023 ∷ Toff023 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ S0 ∷ CS23 ∷ CCZ023 ∷ K0 ∷ CS23 ∷ CX02 ∷ Sw01 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CS01⁻ ∷ [])
  b11 = at 2 2 (CS01 ∷ CS23 ∷ []) (lem-pass-CS23-vs-CS01) ▸
       at 1 2 (CS01 ∷ S0 ∷ []) (lem-pass-S0-vs-CS01) ▸
       at 6 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 5 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 6 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 7 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸ done

  b12 : Chain (Toff023 ∷ CS01 ∷ S0 ∷ CS23 ∷ CCZ023 ∷ K0 ∷ CS23 ∷ CX02 ∷ Sw01 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ S0 ∷ CS23 ∷ CCZ023 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ Sw01 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CS01⁻ ∷ [])
  b12 = at 8 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 9 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 11 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 12 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸ done

  b13 : Chain (Toff023 ∷ CS01 ∷ S0 ∷ CS23 ∷ CCZ023 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ Sw01 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ S0 ∷ CS23 ∷ CCZ023 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ K1 ∷ ι1 ∷ Sw01 ∷ CS01⁻ ∷ [])
  b13 = at 12 2 (ι ∷ Sw01 ∷ []) wn00122 ▸
       at 13 2 [] wn00031 ▸
       at 12 2 (Sw01 ∷ ι1 ∷ []) wn00127 ▸
       at 11 2 (Sw01 ∷ K1 ∷ []) wn00118 ▸
       at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 11 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 10 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b14 : Chain (Toff023 ∷ CS01 ∷ S0 ∷ CS23 ∷ CCZ023 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ K1 ∷ ι1 ∷ Sw01 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ S0 ∷ CS23 ∷ CCZ023 ∷ Sw01 ∷ Toff123 ∷ Sw01 ∷ CS01⁻ ∷ [])
  b14 = at 11 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸
       at 8 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 7 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸
       at 6 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 5 2 (Sw01 ∷ K1 ∷ []) wn00118 ▸
       at 6 8 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) wn00125 ▸
       at 6 8 (Toff123 ∷ []) (by-assoc Eq.refl) ▸ done

  b15 : Chain (Toff023 ∷ CS01 ∷ S0 ∷ CS23 ∷ CCZ023 ∷ Sw01 ∷ Toff123 ∷ Sw01 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ S0 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Toff123 ∷ Sw01 ∷ CS01⁻ ∷ [])
  b15 = at 4 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 5 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 6 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 7 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b16 : Chain (Toff023 ∷ CS01 ∷ S0 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Toff123 ∷ Sw01 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ S0 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Toff123 ∷ Sw01 ∷ CS01⁻ ∷ [])
  b16 = at 9 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00031 ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 9 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 8 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b17 : Chain (Toff023 ∷ CS01 ∷ S0 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Toff123 ∷ Sw01 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ S0 ∷ CS23 ∷ Sw01 ∷ Toff123 ∷ CZ23 ∷ CCZ123 ∷ Sw01 ∷ CS01⁻ ∷ [])
  b17 = at 9 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸
       at 6 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 5 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸
       at 4 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 5 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸
       at 5 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Toff123 ∷ CZ23 ∷ CCZ123 ∷ []) wn01469 ▸ done

  b18 : Chain (Toff023 ∷ CS01 ∷ S0 ∷ CS23 ∷ Sw01 ∷ Toff123 ∷ CZ23 ∷ CCZ123 ∷ Sw01 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ S0 ∷ CS23 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ K1 ∷ ι1 ∷ CZ23 ∷ CCZ123 ∷ Sw01 ∷ CS01⁻ ∷ [])
  b18 = at 5 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 5 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 6 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 7 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 8 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b19 : Chain (Toff023 ∷ CS01 ∷ S0 ∷ CS23 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ K1 ∷ ι1 ∷ CZ23 ∷ CCZ123 ∷ Sw01 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ S0 ∷ CS23 ∷ Sw01 ∷ K1 ∷ CS23 ∷ Sw01 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ Sw01 ∷ CZ23 ∷ CCZ123 ∷ Sw01 ∷ CS01⁻ ∷ [])
  b19 = at 10 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 11 2 (ι ∷ Sw01 ∷ []) wn00122 ▸
       at 4 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 5 2 (K1 ∷ Sw01 ∷ []) wn00123 ▸
       at 6 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸ done

  b20 : Chain (Toff023 ∷ CS01 ∷ S0 ∷ CS23 ∷ Sw01 ∷ K1 ∷ CS23 ∷ Sw01 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ Sw01 ∷ CZ23 ∷ CCZ123 ∷ Sw01 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ S0 ∷ CS23 ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ K0 ∷ ι ∷ Sw01 ∷ CZ23 ∷ CCZ123 ∷ Sw01 ∷ CS01⁻ ∷ [])
  b20 = at 7 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 8 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 9 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 11 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 12 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b21 : Chain (Toff023 ∷ CS01 ∷ S0 ∷ CS23 ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ K0 ∷ ι ∷ Sw01 ∷ CZ23 ∷ CCZ123 ∷ Sw01 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ S0 ∷ CS23 ∷ Toff023 ∷ CZ23 ∷ CS23 ∷ Sw01 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ CS01⁻ ∷ [])
  b21 = at 11 2 (K1 ∷ Sw01 ∷ []) wn00123 ▸
       at 12 2 (ι1 ∷ Sw01 ∷ []) wn00124 ▸
       at 5 8 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) wn00125 ▸
       at 5 8 (Toff123 ∷ []) (by-assoc Eq.refl) ▸
       at 4 3 (Toff023 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CZ23 ∷ Sw01 ∷ []) (low-comm (Swap) (CZ)) ▸
       at 7 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸ done

  b22 : Chain (Toff023 ∷ CS01 ∷ S0 ∷ CS23 ∷ Toff023 ∷ CZ23 ∷ CS23 ∷ Sw01 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ S0 ∷ CS23 ∷ Toff023 ∷ CZ23 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ Sw01 ∷ CS01⁻ ∷ [])
  b22 = at 7 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 8 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 9 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 11 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 12 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b23 : Chain (Toff023 ∷ CS01 ∷ S0 ∷ CS23 ∷ Toff023 ∷ CZ23 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ Sw01 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ S0 ∷ CS23 ∷ Toff023 ∷ CZ23 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ CS12 ∷ Sw01 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ CS01⁻ ∷ [])
  b23 = at 6 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 7 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 8 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 9 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 10 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 12 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸ done

  b24 : Chain (Toff023 ∷ CS01 ∷ S0 ∷ CS23 ∷ Toff023 ∷ CZ23 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ CS12 ∷ Sw01 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ S0 ∷ CS23 ∷ Sw01 ∷ Toff123 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ [])
  b24 = at 13 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 11 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸
       at 7 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 6 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00031 ▸
       at 5 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 4 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸ done

  b25 : Chain (Toff023 ∷ CS01 ∷ S0 ∷ CS23 ∷ Sw01 ∷ Toff123 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ S0 ∷ CS23 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ [])
  b25 = at 5 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 5 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 6 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 7 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 8 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b26 : Chain (Toff023 ∷ CS01 ∷ S0 ∷ CS23 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ S0 ∷ CS23 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ K1 ∷ ι1 ∷ Sw01 ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ [])
  b26 = at 10 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 11 2 (ι ∷ Sw01 ∷ []) wn00122 ▸
       at 12 2 [] wn00031 ▸
       at 11 2 (Sw01 ∷ ι1 ∷ []) wn00127 ▸
       at 10 2 (Sw01 ∷ K1 ∷ []) wn00118 ▸ done

  b27 : Chain (Toff023 ∷ CS01 ∷ S0 ∷ CS23 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ K1 ∷ ι1 ∷ Sw01 ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ S0 ∷ CS23 ∷ K0 ∷ CS23 ∷ Sw01 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ [])
  b27 = at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 10 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 9 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 10 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸
       at 7 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 6 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸ done

  b28 : Chain (Toff023 ∷ CS01 ∷ S0 ∷ CS23 ∷ K0 ∷ CS23 ∷ Sw01 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ S0 ∷ K0 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ CS23 ∷ Sw01 ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ [])
  b28 = at 5 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 4 2 (Sw01 ∷ K1 ∷ []) wn00118 ▸
       at 5 8 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) wn00125 ▸
       at 5 8 (Toff123 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 4 2 (Toff123 ∷ CS23 ∷ []) wn01374 ▸
       at 4 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸ done

  b29 : Chain (Toff023 ∷ CS01 ∷ S0 ∷ K0 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ CS23 ∷ Sw01 ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ S0 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ K1 ∷ ι1 ∷ CS23 ∷ Sw01 ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ [])
  b29 = at 4 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 5 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 6 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 7 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b30 : Chain (Toff023 ∷ CS01 ∷ S0 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ K1 ∷ ι1 ∷ CS23 ∷ Sw01 ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ S0 ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ Sw01 ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ Sw01 ∷ CS23 ∷ Sw01 ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ [])
  b30 = at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 10 2 (ι ∷ Sw01 ∷ []) wn00122 ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 4 2 (K1 ∷ Sw01 ∷ []) wn00123 ▸
       at 5 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 6 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 7 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸ done

  b31 : Chain (Toff023 ∷ CS01 ∷ S0 ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ Sw01 ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ Sw01 ∷ CS23 ∷ Sw01 ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ S0 ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ Sw01 ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ [])
  b31 = at 8 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (K1 ∷ Sw01 ∷ []) wn00123 ▸
       at 11 2 (ι1 ∷ Sw01 ∷ []) wn00124 ▸ done

  b32 : Chain (Toff023 ∷ CS01 ∷ S0 ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ Sw01 ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ S0 ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ [])
  b32 = at 4 8 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) wn00125 ▸
       at 4 8 (Toff123 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (Toff023 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 5 2 [] wn00031 ▸
       at 4 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 3 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸ done

  b33 : Chain (Toff023 ∷ CS01 ∷ S0 ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ S0 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ [])
  b33 = at 3 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 4 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 5 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 6 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 7 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸ done

  b34 : Chain (Toff023 ∷ CS01 ∷ S0 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ S0 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ K1 ∷ ι1 ∷ Sw01 ∷ CS23 ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ [])
  b34 = at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 10 2 (ι ∷ Sw01 ∷ []) wn00122 ▸
       at 11 2 [] wn00031 ▸
       at 10 2 (Sw01 ∷ ι1 ∷ []) wn00127 ▸
       at 9 2 (Sw01 ∷ K1 ∷ []) wn00118 ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b35 : Chain (Toff023 ∷ CS01 ∷ S0 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ K1 ∷ ι1 ∷ Sw01 ∷ CS23 ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ S0 ∷ K0 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ CS23 ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ [])
  b35 = at 10 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 9 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 8 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 9 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸
       at 6 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 5 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸
       at 4 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸ done

  b36 : Chain (Toff023 ∷ CS01 ∷ S0 ∷ K0 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ CS23 ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ K0 ∷ CS23 ∷ Sw01 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ S1 ∷ CS23 ∷ CCZ123 ∷ Sw01 ∷ CS23 ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ [])
  b36 = at 3 2 (Sw01 ∷ K1 ∷ []) wn00118 ▸
       at 4 8 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) wn00125 ▸
       at 4 8 (Toff123 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw01 ∷ S1 ∷ []) wn00481 ▸
       at 3 2 (Toff123 ∷ S1 ∷ CS23 ∷ CCZ123 ∷ []) wn01468 ▸
       at 3 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 3 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸ done

  b37 : Chain (Toff023 ∷ CS01 ∷ K0 ∷ CS23 ∷ Sw01 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ S1 ∷ CS23 ∷ CCZ123 ∷ Sw01 ∷ CS23 ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ K1 ∷ ι1 ∷ S1 ∷ CS23 ∷ CCZ123 ∷ Sw01 ∷ CS23 ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ [])
  b37 = at 4 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 5 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 6 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b38 : Chain (Toff023 ∷ CS01 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ K1 ∷ ι1 ∷ S1 ∷ CS23 ∷ CCZ123 ∷ Sw01 ∷ CS23 ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw01 ∷ S1 ∷ CS23 ∷ CCZ123 ∷ Sw01 ∷ CS23 ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ [])
  b38 = at 8 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 9 2 (ι ∷ Sw01 ∷ []) wn00122 ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 3 2 (K1 ∷ Sw01 ∷ []) wn00123 ▸
       at 4 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 5 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 6 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 7 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸ done

  b39 : Chain (Toff023 ∷ CS01 ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw01 ∷ S1 ∷ CS23 ∷ CCZ123 ∷ Sw01 ∷ CS23 ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ S1 ∷ CS23 ∷ CCZ123 ∷ Sw01 ∷ CS23 ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ [])
  b39 = at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K1 ∷ Sw01 ∷ []) wn00123 ▸
       at 10 2 (ι1 ∷ Sw01 ∷ []) wn00124 ▸
       at 3 8 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) wn00125 ▸ done

  b40 : Chain (Toff023 ∷ CS01 ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ S1 ∷ CS23 ∷ CCZ123 ∷ Sw01 ∷ CS23 ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ Toff023 ∷ S0 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ CS13 ∷ Sw01 ∷ CS23 ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ [])
  b40 = at 3 8 (Toff123 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff023 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (S0 ∷ Sw01 ∷ []) wn00315 ▸
       at 4 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 6 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 6 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 7 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸ done

  b41 : Chain (Toff023 ∷ CS01 ∷ Toff023 ∷ S0 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ CS13 ∷ Sw01 ∷ CS23 ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ Toff023 ∷ S0 ∷ CS23 ∷ Sw01 ∷ CS23 ∷ Sw01 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ [])
  b41 = at 8 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 6 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸ done

  b42 : Chain (Toff023 ∷ CS01 ∷ Toff023 ∷ S0 ∷ CS23 ∷ Sw01 ∷ CS23 ∷ Sw01 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ Toff023 ∷ S0 ∷ CS23 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ [])
  b42 = at 7 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 8 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 9 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 11 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 12 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b43 : Chain (Toff023 ∷ CS01 ∷ Toff023 ∷ S0 ∷ CS23 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CZ23 ∷ CCZ023 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ Toff023 ∷ S0 ∷ CCZ023 ∷ CCZ023 ∷ Sw01 ∷ Sw01 ∷ CS01⁻ ∷ [])
  b43 = at 6 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸
       at 6 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00031 ▸
       at 5 2 (CS23 ∷ CCZ023 ∷ []) (lem-pass-CCZ023-vs-CS23) ▸
       at 6 2 (CZ23 ∷ CCZ023 ∷ []) (lem-pass-CCZ023-vs-CZ23) ▸
       at 4 3 [] wn01470 ▸
       at 6 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸ done

  b44 : Chain (Toff023 ∷ CS01 ∷ Toff023 ∷ S0 ∷ CCZ023 ∷ CCZ023 ∷ Sw01 ∷ Sw01 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ Toff023 ∷ S0 ∷ CCZ023 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CS01⁻ ∷ [])
  b44 = at 5 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 6 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 7 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 8 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b45 : Chain (Toff023 ∷ CS01 ∷ Toff023 ∷ S0 ∷ CCZ023 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ Toff023 ∷ S0 ∷ CCZ023 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ CS01⁻ ∷ [])
  b45 = at 10 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00031 ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 10 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 9 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b46 : Chain (Toff023 ∷ CS01 ∷ Toff023 ∷ S0 ∷ CCZ023 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ Toff023 ∷ S0 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ CS01⁻ ∷ [])
  b46 = at 10 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸
       at 7 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 6 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸
       at 5 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 6 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸
       at 6 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸ done

  b47 : Chain (Toff023 ∷ CS01 ∷ Toff023 ∷ S0 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ Toff023 ∷ S0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ CS01⁻ ∷ [])
  b47 = at 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 5 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 6 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 7 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸ done

  b48 : Chain (Toff023 ∷ CS01 ∷ Toff023 ∷ S0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ Toff023 ∷ S0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ CCZ123 ∷ Sw01 ∷ CS01⁻ ∷ [])
  b48 = at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00031 ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 9 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 8 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 9 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b49 : Chain (Toff023 ∷ CS01 ∷ Toff023 ∷ S0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ CCZ123 ∷ Sw01 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ Toff023 ∷ S0 ∷ CS01⁻ ∷ [])
  b49 = at 7 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸
       at 6 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 5 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸
       at 4 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 5 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸
       at 5 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00033 ▸
       at 4 2 [] wn00031 ▸ done

  b50 : Chain (Toff023 ∷ CS01 ∷ Toff023 ∷ S0 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ S0 ∷ [])
  b50 = at 3 2 (CS01⁻ ∷ S0 ∷ []) (lem-pass-S0-vs-CSd01) ▸ done

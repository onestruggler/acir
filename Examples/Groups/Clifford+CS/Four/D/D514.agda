{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D514 where

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
open import Examples.Groups.Clifford+CS.Four.Wins.W01 using (wn00005 ; wn00006 ; wn00007 ; wn00024 ; wn00025 ; wn00027 ; wn00030 ; wn00031 ; wn00039 ; wn00074 ; wn00118 ; wn00121 ; wn00122 ; wn00123 ; wn00124 ; wn00125 ; wn00127)
open import Examples.Groups.Clifford+CS.Four.Wins.W26 using (wn01327)
open import Examples.Groups.Clifford+CS.Four.Wins.W27 using (wn01373 ; wn01374 ; wn01375 ; wn01376 ; wn01377 ; wn01378 ; wn01379 ; wn01380 ; wn01381)
open import Examples.Groups.Clifford+CS.Canonical using (can-≈)
open import Examples.Groups.Clifford+CS.Four.D.D013 using (lem-pass-CS23-vs-CS01)
open import Examples.Groups.Clifford+CS.Four.D.D014 using (lem-pass-X3-CK31-X3-vs-TOFF102-CS13-TOFF102-CSd13 ; lem-pass-X3-CS31-X3-vs-CS02)
open import Examples.Groups.Clifford+CS.Four.D.D015 using (lem-pass-X3-CK31-X3-vs-CS02 ; lem-pass-X3-CK31-X3-vs-CSd02 ; lem-pass-X3-CK31-X3-vs-TOFF013 ; lem-pass-X3-CS31-X3-vs-CSd02 ; lem-pass-X3-CS31-X3-vs-TOFF013)
open import Examples.Groups.Clifford+CS.Four.D.D021 using (lem-pass-CS23-vs-CSd01)
open import Examples.Groups.Clifford+CS.Four.D.D022 using (lem-comm-CCZ013-CCZ123)
open import Examples.Groups.Clifford+CS.Four.D.D023 using (lem-pass-X3-CK32-X3-vs-CS01 ; lem-pass-X3-CK32-X3-vs-CSd01 ; lem-pass-X3-CK32-X3-vs-TOFF023)

-- pass [CS23] [X3 TOFF023 X3 CS01 X3 TOFF023 X3 CSd01]: 398 steps
lem-pass-CS23-vs-X3-TOFF023-X3-CS01-X3-TOFF023-X3-CSd01 : ⟪ (CS23 ∷ X3 ∷ Toff023 ∷ X3 ∷ CS01 ∷ X3 ∷ Toff023 ∷ X3 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff023 ∷ X3 ∷ CS01 ∷ X3 ∷ Toff023 ∷ X3 ∷ CS01⁻ ∷ CS23 ∷ []) ⟫ʷ
lem-pass-CS23-vs-X3-TOFF023-X3-CS01-X3-TOFF023-X3-CSd01 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (trans (run b38) (trans (run b39) (trans (run b40) (trans (run b41) (trans (run b42) (trans (run b43) (trans (run b44) (trans (run b45) (trans (run b46) (trans (run b47) (trans (run b48) (run b49)))))))))))))))))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (CS23 ∷ X3 ∷ Toff023 ∷ X3 ∷ CS01 ∷ X3 ∷ Toff023 ∷ X3 ∷ CS01⁻ ∷ []) (CS23 ∷ X3 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ X3 ∷ Sw01 ∷ CS01 ∷ X3 ∷ Toff023 ∷ X3 ∷ CS01⁻ ∷ [])
  b0 = at 4 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 3 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸
       at 2 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 3 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 4 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 5 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸ done

  b1 : Chain (CS23 ∷ X3 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ X3 ∷ Sw01 ∷ CS01 ∷ X3 ∷ Toff023 ∷ X3 ∷ CS01⁻ ∷ []) (CS23 ∷ X3 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ X3 ∷ Sw01 ∷ CS01 ∷ X3 ∷ Toff023 ∷ X3 ∷ CS01⁻ ∷ [])
  b1 = at 6 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 9 2 (ι ∷ Sw01 ∷ []) wn00122 ▸ done

  b2 : Chain (CS23 ∷ X3 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ X3 ∷ Sw01 ∷ CS01 ∷ X3 ∷ Toff023 ∷ X3 ∷ CS01⁻ ∷ []) (CS23 ∷ X3 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ K1 ∷ ι1 ∷ X3 ∷ Sw01 ∷ CS01 ∷ X3 ∷ Toff023 ∷ X3 ∷ CS01⁻ ∷ [])
  b2 = at 10 2 [] wn00031 ▸
       at 9 2 (Sw01 ∷ ι1 ∷ []) wn00127 ▸
       at 8 2 (Sw01 ∷ K1 ∷ []) wn00118 ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 8 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 7 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 8 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (CS23 ∷ X3 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ K1 ∷ ι1 ∷ X3 ∷ Sw01 ∷ CS01 ∷ X3 ∷ Toff023 ∷ X3 ∷ CS01⁻ ∷ []) (CS23 ∷ Sw01 ∷ X3 ∷ Toff123 ∷ X3 ∷ Sw01 ∷ CS01 ∷ X3 ∷ Toff023 ∷ X3 ∷ CS01⁻ ∷ [])
  b3 = at 6 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸
       at 5 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 4 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸
       at 3 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 2 2 (Sw01 ∷ K1 ∷ []) wn00118 ▸
       at 3 8 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) wn00125 ▸
       at 3 8 (Toff123 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸ done

  b4 : Chain (CS23 ∷ Sw01 ∷ X3 ∷ Toff123 ∷ X3 ∷ Sw01 ∷ CS01 ∷ X3 ∷ Toff023 ∷ X3 ∷ CS01⁻ ∷ []) (CS23 ∷ CX20 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ CS01 ∷ X3 ∷ Toff023 ∷ X3 ∷ CS01⁻ ∷ [])
  b4 = at 2 3 (CX21 ∷ Toff123 ∷ []) wn01373 ▸
       at 1 2 (CX20 ∷ Sw01 ∷ []) wn00039 ▸
       at 3 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 3 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 4 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 5 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 6 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸ done

  b5 : Chain (CS23 ∷ CX20 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ CS01 ∷ X3 ∷ Toff023 ∷ X3 ∷ CS01⁻ ∷ []) (CS23 ∷ CX20 ∷ Sw01 ∷ Sw01 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ Sw01 ∷ Sw01 ∷ CS01 ∷ X3 ∷ Toff023 ∷ X3 ∷ CS01⁻ ∷ [])
  b5 = at 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 9 2 (ι ∷ Sw01 ∷ []) wn00122 ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸ done

  b6 : Chain (CS23 ∷ CX20 ∷ Sw01 ∷ Sw01 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ Sw01 ∷ Sw01 ∷ CS01 ∷ X3 ∷ Toff023 ∷ X3 ∷ CS01⁻ ∷ []) (CS23 ∷ CX20 ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ CS12 ∷ Sw01 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw01 ∷ Sw01 ∷ CS01 ∷ X3 ∷ Toff023 ∷ X3 ∷ CS01⁻ ∷ [])
  b6 = at 3 2 (K1 ∷ Sw01 ∷ []) wn00123 ▸
       at 4 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 5 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 6 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 7 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸ done

  b7 : Chain (CS23 ∷ CX20 ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ CS12 ∷ Sw01 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw01 ∷ Sw01 ∷ CS01 ∷ X3 ∷ Toff023 ∷ X3 ∷ CS01⁻ ∷ []) (CS23 ∷ CX20 ∷ Toff023 ∷ CS01 ∷ X3 ∷ Toff023 ∷ X3 ∷ CS01⁻ ∷ [])
  b7 = at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K1 ∷ Sw01 ∷ []) wn00123 ▸
       at 10 2 (ι1 ∷ Sw01 ∷ []) wn00124 ▸
       at 3 8 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) wn00125 ▸
       at 3 8 (Toff123 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff023 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00031 ▸ done

  b8 : Chain (CS23 ∷ CX20 ∷ Toff023 ∷ CS01 ∷ X3 ∷ Toff023 ∷ X3 ∷ CS01⁻ ∷ []) (CX20 ∷ CS23 ∷ Toff023 ∷ Sw01 ∷ Sw01 ∷ CS01 ∷ X3 ∷ Toff023 ∷ X3 ∷ CS01⁻ ∷ [])
  b8 = at 2 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 1 2 (Sw01 ∷ CX21 ∷ []) wn00006 ▸
       at 0 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 1 2 (CX21 ∷ CS23 ∷ []) wn01327 ▸
       at 0 2 (CX20 ∷ Sw01 ∷ []) wn00039 ▸
       at 1 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 2 2 [] wn00031 ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸ done

  b9 : Chain (CX20 ∷ CS23 ∷ Toff023 ∷ Sw01 ∷ Sw01 ∷ CS01 ∷ X3 ∷ Toff023 ∷ X3 ∷ CS01⁻ ∷ []) (CX20 ∷ CS23 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CS01 ∷ X3 ∷ Toff023 ∷ X3 ∷ CS01⁻ ∷ [])
  b9 = at 2 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 3 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 4 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 5 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 6 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b10 : Chain (CX20 ∷ CS23 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CS01 ∷ X3 ∷ Toff023 ∷ X3 ∷ CS01⁻ ∷ []) (CX20 ∷ CS23 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ Sw01 ∷ ι1 ∷ Sw01 ∷ CS01 ∷ X3 ∷ Toff023 ∷ X3 ∷ CS01⁻ ∷ [])
  b10 = at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 9 2 (ι ∷ Sw01 ∷ []) wn00122 ▸
       at 10 2 [] wn00031 ▸
       at 9 2 (Sw01 ∷ ι1 ∷ []) wn00127 ▸ done

  b11 : Chain (CX20 ∷ CS23 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ Sw01 ∷ ι1 ∷ Sw01 ∷ CS01 ∷ X3 ∷ Toff023 ∷ X3 ∷ CS01⁻ ∷ []) (CX20 ∷ CS23 ∷ K0 ∷ CS23 ∷ CX02 ∷ Sw01 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ CS01 ∷ X3 ∷ Toff023 ∷ X3 ∷ CS01⁻ ∷ [])
  b11 = at 8 2 (Sw01 ∷ K1 ∷ []) wn00118 ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 8 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 7 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 8 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸
       at 5 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸ done

  b12 : Chain (CX20 ∷ CS23 ∷ K0 ∷ CS23 ∷ CX02 ∷ Sw01 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ CS01 ∷ X3 ∷ Toff023 ∷ X3 ∷ CS01⁻ ∷ []) (CX20 ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ CS23 ∷ Sw01 ∷ CS01 ∷ X3 ∷ Toff023 ∷ X3 ∷ CS01⁻ ∷ [])
  b12 = at 4 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸
       at 3 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 2 2 (Sw01 ∷ K1 ∷ []) wn00118 ▸
       at 3 8 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) wn00125 ▸
       at 3 8 (Toff123 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 2 2 (Toff123 ∷ CS23 ∷ []) wn01374 ▸
       at 2 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸ done

  b13 : Chain (CX20 ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ CS23 ∷ Sw01 ∷ CS01 ∷ X3 ∷ Toff023 ∷ X3 ∷ CS01⁻ ∷ []) (CX20 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ K1 ∷ ι1 ∷ CS23 ∷ Sw01 ∷ CS01 ∷ X3 ∷ Toff023 ∷ X3 ∷ CS01⁻ ∷ [])
  b13 = at 1 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 2 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 3 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 4 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 5 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸ done

  b14 : Chain (CX20 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ K1 ∷ ι1 ∷ CS23 ∷ Sw01 ∷ CS01 ∷ X3 ∷ Toff023 ∷ X3 ∷ CS01⁻ ∷ []) (CX20 ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ Sw01 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ Sw01 ∷ CS23 ∷ Sw01 ∷ CS01 ∷ X3 ∷ Toff023 ∷ X3 ∷ CS01⁻ ∷ [])
  b14 = at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 8 2 (ι ∷ Sw01 ∷ []) wn00122 ▸
       at 1 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 2 2 (K1 ∷ Sw01 ∷ []) wn00123 ▸
       at 3 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 4 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸ done

  b15 : Chain (CX20 ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ Sw01 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ Sw01 ∷ CS23 ∷ Sw01 ∷ CS01 ∷ X3 ∷ Toff023 ∷ X3 ∷ CS01⁻ ∷ []) (CX20 ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ Sw01 ∷ ι ∷ Sw01 ∷ CS23 ∷ Sw01 ∷ CS01 ∷ X3 ∷ Toff023 ∷ X3 ∷ CS01⁻ ∷ [])
  b15 = at 5 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 6 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K1 ∷ Sw01 ∷ []) wn00123 ▸ done

  b16 : Chain (CX20 ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ Sw01 ∷ ι ∷ Sw01 ∷ CS23 ∷ Sw01 ∷ CS01 ∷ X3 ∷ Toff023 ∷ X3 ∷ CS01⁻ ∷ []) (CX20 ∷ Sw01 ∷ Toff123 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CS01 ∷ X3 ∷ Toff023 ∷ X3 ∷ CS01⁻ ∷ [])
  b16 = at 9 2 (ι1 ∷ Sw01 ∷ []) wn00124 ▸
       at 2 8 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) wn00125 ▸
       at 2 8 (Toff123 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff023 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 3 2 [] wn00031 ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 1 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸ done

  b17 : Chain (CX20 ∷ Sw01 ∷ Toff123 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CS01 ∷ X3 ∷ Toff023 ∷ X3 ∷ CS01⁻ ∷ []) (CX20 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CS01 ∷ X3 ∷ Toff023 ∷ X3 ∷ CS01⁻ ∷ [])
  b17 = at 2 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 2 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 3 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 4 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 5 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b18 : Chain (CX20 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CS01 ∷ X3 ∷ Toff023 ∷ X3 ∷ CS01⁻ ∷ []) (CX20 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ K1 ∷ ι1 ∷ Sw01 ∷ CS23 ∷ CS01 ∷ X3 ∷ Toff023 ∷ X3 ∷ CS01⁻ ∷ [])
  b18 = at 7 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 8 2 (ι ∷ Sw01 ∷ []) wn00122 ▸
       at 9 2 [] wn00031 ▸
       at 8 2 (Sw01 ∷ ι1 ∷ []) wn00127 ▸
       at 7 2 (Sw01 ∷ K1 ∷ []) wn00118 ▸ done

  b19 : Chain (CX20 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ K1 ∷ ι1 ∷ Sw01 ∷ CS23 ∷ CS01 ∷ X3 ∷ Toff023 ∷ X3 ∷ CS01⁻ ∷ []) (CX20 ∷ K0 ∷ CS23 ∷ Sw01 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ CS23 ∷ CS01 ∷ X3 ∷ Toff023 ∷ X3 ∷ CS01⁻ ∷ [])
  b19 = at 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 7 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 6 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 7 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸
       at 4 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 3 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸ done

  b20 : Chain (CX20 ∷ K0 ∷ CS23 ∷ Sw01 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ CS23 ∷ CS01 ∷ X3 ∷ Toff023 ∷ X3 ∷ CS01⁻ ∷ []) (X3 ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ X3 ∷ Sw01 ∷ CS23 ∷ CS01 ∷ X3 ∷ Toff023 ∷ X3 ∷ CS01⁻ ∷ [])
  b20 = at 2 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 1 2 (Sw01 ∷ K1 ∷ []) wn00118 ▸
       at 2 8 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) wn00125 ▸
       at 2 8 (Toff123 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw01 ∷ CX21 ∷ []) wn00006 ▸
       at 1 2 (X3 ∷ Toff123 ∷ X3 ∷ []) wn01375 ▸
       at 0 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸
       at 2 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸ done

  b21 : Chain (X3 ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ X3 ∷ Sw01 ∷ CS23 ∷ CS01 ∷ X3 ∷ Toff023 ∷ X3 ∷ CS01⁻ ∷ []) (X3 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ K1 ∷ ι1 ∷ X3 ∷ Sw01 ∷ CS23 ∷ CS01 ∷ X3 ∷ Toff023 ∷ X3 ∷ CS01⁻ ∷ [])
  b21 = at 1 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 2 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 3 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 4 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 5 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸ done

  b22 : Chain (X3 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ K1 ∷ ι1 ∷ X3 ∷ Sw01 ∷ CS23 ∷ CS01 ∷ X3 ∷ Toff023 ∷ X3 ∷ CS01⁻ ∷ []) (X3 ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ Sw01 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ Sw01 ∷ X3 ∷ Sw01 ∷ CS23 ∷ CS01 ∷ X3 ∷ Toff023 ∷ X3 ∷ CS01⁻ ∷ [])
  b22 = at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 8 2 (ι ∷ Sw01 ∷ []) wn00122 ▸
       at 1 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 2 2 (K1 ∷ Sw01 ∷ []) wn00123 ▸
       at 3 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 4 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸ done

  b23 : Chain (X3 ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ Sw01 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ Sw01 ∷ X3 ∷ Sw01 ∷ CS23 ∷ CS01 ∷ X3 ∷ Toff023 ∷ X3 ∷ CS01⁻ ∷ []) (X3 ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ Sw01 ∷ ι ∷ Sw01 ∷ X3 ∷ Sw01 ∷ CS23 ∷ CS01 ∷ X3 ∷ Toff023 ∷ X3 ∷ CS01⁻ ∷ [])
  b23 = at 5 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 6 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K1 ∷ Sw01 ∷ []) wn00123 ▸ done

  b24 : Chain (X3 ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ Sw01 ∷ ι ∷ Sw01 ∷ X3 ∷ Sw01 ∷ CS23 ∷ CS01 ∷ X3 ∷ Toff023 ∷ X3 ∷ CS01⁻ ∷ []) (X3 ∷ Toff023 ∷ X3 ∷ CS01 ∷ CS23 ∷ X3 ∷ Toff023 ∷ X3 ∷ Sw01 ∷ Sw01 ∷ CS01⁻ ∷ [])
  b24 = at 9 2 (ι1 ∷ Sw01 ∷ []) wn00124 ▸
       at 2 8 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) wn00125 ▸
       at 2 8 (Toff123 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff023 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸
       at 3 2 [] wn00031 ▸
       at 3 2 (CS01 ∷ CS23 ∷ []) (lem-pass-CS23-vs-CS01) ▸
       at 8 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸ done

  b25 : Chain (X3 ∷ Toff023 ∷ X3 ∷ CS01 ∷ CS23 ∷ X3 ∷ Toff023 ∷ X3 ∷ Sw01 ∷ Sw01 ∷ CS01⁻ ∷ []) (X3 ∷ Toff023 ∷ X3 ∷ CS01 ∷ CS23 ∷ X3 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ X3 ∷ Sw01 ∷ CS01⁻ ∷ [])
  b25 = at 7 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸
       at 6 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 7 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 8 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 9 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 10 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸ done

  b26 : Chain (X3 ∷ Toff023 ∷ X3 ∷ CS01 ∷ CS23 ∷ X3 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ X3 ∷ Sw01 ∷ CS01⁻ ∷ []) (X3 ∷ Toff023 ∷ X3 ∷ CS01 ∷ CS23 ∷ X3 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ Sw01 ∷ X3 ∷ Sw01 ∷ CS01⁻ ∷ [])
  b26 = at 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 12 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 13 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 11 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 13 2 (ι ∷ Sw01 ∷ []) wn00122 ▸
       at 14 2 [] wn00031 ▸ done

  b27 : Chain (X3 ∷ Toff023 ∷ X3 ∷ CS01 ∷ CS23 ∷ X3 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ Sw01 ∷ X3 ∷ Sw01 ∷ CS01⁻ ∷ []) (X3 ∷ Toff023 ∷ X3 ∷ CS01 ∷ CS23 ∷ X3 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ X3 ∷ Sw01 ∷ CS01⁻ ∷ [])
  b27 = at 13 2 (Sw01 ∷ ι1 ∷ []) wn00127 ▸
       at 12 2 (Sw01 ∷ K1 ∷ []) wn00118 ▸
       at 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 12 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 11 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 12 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸ done

  b28 : Chain (X3 ∷ Toff023 ∷ X3 ∷ CS01 ∷ CS23 ∷ X3 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ X3 ∷ Sw01 ∷ CS01⁻ ∷ []) (X3 ∷ Toff023 ∷ X3 ∷ CS01 ∷ CS23 ∷ Sw01 ∷ CX21 ∷ Toff123 ∷ Sw01 ∷ CS01⁻ ∷ [])
  b28 = at 9 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 8 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸
       at 7 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 6 2 (Sw01 ∷ K1 ∷ []) wn00118 ▸
       at 7 8 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) wn00125 ▸
       at 7 8 (Toff123 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸
       at 6 3 (CX21 ∷ Toff123 ∷ []) wn01373 ▸ done

  b29 : Chain (X3 ∷ Toff023 ∷ X3 ∷ CS01 ∷ CS23 ∷ Sw01 ∷ CX21 ∷ Toff123 ∷ Sw01 ∷ CS01⁻ ∷ []) (X3 ∷ Toff023 ∷ X3 ∷ CS01 ∷ CS23 ∷ CX20 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ K1 ∷ ι1 ∷ Sw01 ∷ CS01⁻ ∷ [])
  b29 = at 5 2 (CX20 ∷ Sw01 ∷ []) wn00039 ▸
       at 7 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 7 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 8 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 9 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 10 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b30 : Chain (X3 ∷ Toff023 ∷ X3 ∷ CS01 ∷ CS23 ∷ CX20 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ K1 ∷ ι1 ∷ Sw01 ∷ CS01⁻ ∷ []) (X3 ∷ Toff023 ∷ X3 ∷ CS01 ∷ CS23 ∷ CX20 ∷ Sw01 ∷ K1 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ Sw01 ∷ Sw01 ∷ CS01⁻ ∷ [])
  b30 = at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 12 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 13 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 11 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 13 2 (ι ∷ Sw01 ∷ []) wn00122 ▸
       at 6 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 7 2 (K1 ∷ Sw01 ∷ []) wn00123 ▸ done

  b31 : Chain (X3 ∷ Toff023 ∷ X3 ∷ CS01 ∷ CS23 ∷ CX20 ∷ Sw01 ∷ K1 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ Sw01 ∷ Sw01 ∷ CS01⁻ ∷ []) (X3 ∷ Toff023 ∷ X3 ∷ CS01 ∷ CS23 ∷ CX20 ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ K0 ∷ ι ∷ Sw01 ∷ Sw01 ∷ CS01⁻ ∷ [])
  b31 = at 8 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 9 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 10 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 11 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 13 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 14 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b32 : Chain (X3 ∷ Toff023 ∷ X3 ∷ CS01 ∷ CS23 ∷ CX20 ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ K0 ∷ ι ∷ Sw01 ∷ Sw01 ∷ CS01⁻ ∷ []) (X3 ∷ Toff023 ∷ X3 ∷ CS01 ∷ CS23 ∷ CX20 ∷ Sw01 ∷ Sw01 ∷ Toff023 ∷ CS01⁻ ∷ [])
  b32 = at 12 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (K1 ∷ Sw01 ∷ []) wn00123 ▸
       at 14 2 (ι1 ∷ Sw01 ∷ []) wn00124 ▸
       at 7 8 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) wn00125 ▸
       at 7 8 (Toff123 ∷ []) (by-assoc Eq.refl) ▸
       at 6 3 (Toff023 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00031 ▸
       at 6 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸ done

  b33 : Chain (X3 ∷ Toff023 ∷ X3 ∷ CS01 ∷ CS23 ∷ CX20 ∷ Sw01 ∷ Sw01 ∷ Toff023 ∷ CS01⁻ ∷ []) (X3 ∷ Toff023 ∷ X3 ∷ CS01 ∷ CX20 ∷ CS23 ∷ Sw01 ∷ Toff123 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CS01⁻ ∷ [])
  b33 = at 5 2 (Sw01 ∷ CX21 ∷ []) wn00006 ▸
       at 4 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 5 2 (CX21 ∷ CS23 ∷ []) wn01327 ▸
       at 4 2 (CX20 ∷ Sw01 ∷ []) wn00039 ▸
       at 5 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 6 2 [] wn00031 ▸
       at 7 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 6 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸ done

  b34 : Chain (X3 ∷ Toff023 ∷ X3 ∷ CS01 ∷ CX20 ∷ CS23 ∷ Sw01 ∷ Toff123 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CS01⁻ ∷ []) (X3 ∷ Toff023 ∷ X3 ∷ CS01 ∷ CX20 ∷ CS23 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CS01⁻ ∷ [])
  b34 = at 7 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 7 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 8 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 9 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 10 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b35 : Chain (X3 ∷ Toff023 ∷ X3 ∷ CS01 ∷ CX20 ∷ CS23 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CS01⁻ ∷ []) (X3 ∷ Toff023 ∷ X3 ∷ CS01 ∷ CX20 ∷ CS23 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ K1 ∷ ι1 ∷ Sw01 ∷ CS01⁻ ∷ [])
  b35 = at 12 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 13 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 11 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 13 2 (ι ∷ Sw01 ∷ []) wn00122 ▸
       at 14 2 [] wn00031 ▸
       at 13 2 (Sw01 ∷ ι1 ∷ []) wn00127 ▸
       at 12 2 (Sw01 ∷ K1 ∷ []) wn00118 ▸ done

  b36 : Chain (X3 ∷ Toff023 ∷ X3 ∷ CS01 ∷ CX20 ∷ CS23 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ K1 ∷ ι1 ∷ Sw01 ∷ CS01⁻ ∷ []) (X3 ∷ Toff023 ∷ X3 ∷ CS01 ∷ CX20 ∷ CS23 ∷ K0 ∷ CS23 ∷ Sw01 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ CS01⁻ ∷ [])
  b36 = at 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 12 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 11 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 12 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸
       at 9 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 8 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸ done

  b37 : Chain (X3 ∷ Toff023 ∷ X3 ∷ CS01 ∷ CX20 ∷ CS23 ∷ K0 ∷ CS23 ∷ Sw01 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ CS01⁻ ∷ []) (X3 ∷ Toff023 ∷ X3 ∷ CS01 ∷ CX20 ∷ K0 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ CS23 ∷ Sw01 ∷ CS01⁻ ∷ [])
  b37 = at 7 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 6 2 (Sw01 ∷ K1 ∷ []) wn00118 ▸
       at 7 8 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) wn00125 ▸
       at 7 8 (Toff123 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 6 2 (Toff123 ∷ CS23 ∷ []) wn01374 ▸
       at 6 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸ done

  b38 : Chain (X3 ∷ Toff023 ∷ X3 ∷ CS01 ∷ CX20 ∷ K0 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ CS23 ∷ Sw01 ∷ CS01⁻ ∷ []) (X3 ∷ Toff023 ∷ X3 ∷ CS01 ∷ CX20 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ K1 ∷ ι1 ∷ CS23 ∷ Sw01 ∷ CS01⁻ ∷ [])
  b38 = at 6 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 7 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 8 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 9 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 11 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 12 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b39 : Chain (X3 ∷ Toff023 ∷ X3 ∷ CS01 ∷ CX20 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ K1 ∷ ι1 ∷ CS23 ∷ Sw01 ∷ CS01⁻ ∷ []) (X3 ∷ Toff023 ∷ X3 ∷ CS01 ∷ CX20 ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ Sw01 ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ Sw01 ∷ CS23 ∷ Sw01 ∷ CS01⁻ ∷ [])
  b39 = at 10 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 12 2 (ι ∷ Sw01 ∷ []) wn00122 ▸
       at 5 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 6 2 (K1 ∷ Sw01 ∷ []) wn00123 ▸
       at 7 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 8 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 9 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸ done

  b40 : Chain (X3 ∷ Toff023 ∷ X3 ∷ CS01 ∷ CX20 ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ Sw01 ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ Sw01 ∷ CS23 ∷ Sw01 ∷ CS01⁻ ∷ []) (X3 ∷ Toff023 ∷ X3 ∷ CS01 ∷ CX20 ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ Sw01 ∷ CS01⁻ ∷ [])
  b40 = at 10 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 12 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 13 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 11 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (K1 ∷ Sw01 ∷ []) wn00123 ▸
       at 13 2 (ι1 ∷ Sw01 ∷ []) wn00124 ▸ done

  b41 : Chain (X3 ∷ Toff023 ∷ X3 ∷ CS01 ∷ CX20 ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ Sw01 ∷ CS01⁻ ∷ []) (X3 ∷ Toff023 ∷ X3 ∷ CS01 ∷ CX20 ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CS01⁻ ∷ [])
  b41 = at 6 8 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) wn00125 ▸
       at 6 8 (Toff123 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (Toff023 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 7 2 [] wn00031 ▸
       at 6 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 5 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸ done

  b42 : Chain (X3 ∷ Toff023 ∷ X3 ∷ CS01 ∷ CX20 ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CS01⁻ ∷ []) (X3 ∷ Toff023 ∷ X3 ∷ CS01 ∷ CX20 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CS01⁻ ∷ [])
  b42 = at 5 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 6 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 7 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 8 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 9 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 11 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸ done

  b43 : Chain (X3 ∷ Toff023 ∷ X3 ∷ CS01 ∷ CX20 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CS01⁻ ∷ []) (X3 ∷ Toff023 ∷ X3 ∷ CS01 ∷ CX20 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ K1 ∷ ι1 ∷ Sw01 ∷ CS23 ∷ CS01⁻ ∷ [])
  b43 = at 12 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 12 2 (ι ∷ Sw01 ∷ []) wn00122 ▸
       at 13 2 [] wn00031 ▸
       at 12 2 (Sw01 ∷ ι1 ∷ []) wn00127 ▸
       at 11 2 (Sw01 ∷ K1 ∷ []) wn00118 ▸
       at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b44 : Chain (X3 ∷ Toff023 ∷ X3 ∷ CS01 ∷ CX20 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ K1 ∷ ι1 ∷ Sw01 ∷ CS23 ∷ CS01⁻ ∷ []) (X3 ∷ Toff023 ∷ X3 ∷ CS01 ∷ CX20 ∷ K0 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ CS23 ∷ CS01⁻ ∷ [])
  b44 = at 12 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 11 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 10 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 11 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸
       at 8 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 7 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸
       at 6 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸ done

  b45 : Chain (X3 ∷ Toff023 ∷ X3 ∷ CS01 ∷ CX20 ∷ K0 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ CS23 ∷ CS01⁻ ∷ []) (X3 ∷ Toff023 ∷ X3 ∷ CS01 ∷ X3 ∷ K0 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ X3 ∷ Sw01 ∷ CS23 ∷ CS01⁻ ∷ [])
  b45 = at 5 2 (Sw01 ∷ K1 ∷ []) wn00118 ▸
       at 6 8 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) wn00125 ▸
       at 6 8 (Toff123 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw01 ∷ CX21 ∷ []) wn00006 ▸
       at 5 2 (X3 ∷ Toff123 ∷ X3 ∷ []) wn01375 ▸
       at 4 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸
       at 6 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸ done

  b46 : Chain (X3 ∷ Toff023 ∷ X3 ∷ CS01 ∷ X3 ∷ K0 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ X3 ∷ Sw01 ∷ CS23 ∷ CS01⁻ ∷ []) (X3 ∷ Toff023 ∷ X3 ∷ CS01 ∷ X3 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ K1 ∷ ι1 ∷ X3 ∷ Sw01 ∷ CS23 ∷ CS01⁻ ∷ [])
  b46 = at 6 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 7 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 8 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 9 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 11 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 12 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b47 : Chain (X3 ∷ Toff023 ∷ X3 ∷ CS01 ∷ X3 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ K1 ∷ ι1 ∷ X3 ∷ Sw01 ∷ CS23 ∷ CS01⁻ ∷ []) (X3 ∷ Toff023 ∷ X3 ∷ CS01 ∷ X3 ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ Sw01 ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ Sw01 ∷ X3 ∷ Sw01 ∷ CS23 ∷ CS01⁻ ∷ [])
  b47 = at 10 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 12 2 (ι ∷ Sw01 ∷ []) wn00122 ▸
       at 5 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 6 2 (K1 ∷ Sw01 ∷ []) wn00123 ▸
       at 7 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 8 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 9 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸ done

  b48 : Chain (X3 ∷ Toff023 ∷ X3 ∷ CS01 ∷ X3 ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ Sw01 ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ Sw01 ∷ X3 ∷ Sw01 ∷ CS23 ∷ CS01⁻ ∷ []) (X3 ∷ Toff023 ∷ X3 ∷ CS01 ∷ X3 ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ X3 ∷ Sw01 ∷ CS23 ∷ CS01⁻ ∷ [])
  b48 = at 10 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 12 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 13 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 11 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (K1 ∷ Sw01 ∷ []) wn00123 ▸
       at 13 2 (ι1 ∷ Sw01 ∷ []) wn00124 ▸ done

  b49 : Chain (X3 ∷ Toff023 ∷ X3 ∷ CS01 ∷ X3 ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ X3 ∷ Sw01 ∷ CS23 ∷ CS01⁻ ∷ []) (X3 ∷ Toff023 ∷ X3 ∷ CS01 ∷ X3 ∷ Toff023 ∷ X3 ∷ CS01⁻ ∷ CS23 ∷ [])
  b49 = at 6 8 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) wn00125 ▸
       at 6 8 (Toff123 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (Toff023 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸
       at 7 2 [] wn00031 ▸
       at 7 2 (CS01⁻ ∷ CS23 ∷ []) (lem-pass-CS23-vs-CSd01) ▸ done

-- pass [CCZ013] [CCZ123]: 1 steps
lem-pass-CCZ013-vs-CCZ123 : ⟪ (CCZ013 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CCZ013 ∷ []) ⟫ʷ
lem-pass-CCZ013-vs-CCZ123 = run b0
  where
  b0 : Chain (CCZ013 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ013 ∷ [])
  b0 = at 0 2 (CCZ123 ∷ CCZ013 ∷ []) (lem-comm-CCZ013-CCZ123) ▸ done

-- pass [X3 CK32 X3] [TOFF023 CS01 TOFF023 CSd01]: 4 steps
lem-pass-X3-CK32-X3-vs-TOFF023-CS01-TOFF023-CSd01 : ⟪ (X3 ∷ CK32 ∷ X3 ∷ Toff023 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ X3 ∷ CK32 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CK32-X3-vs-TOFF023-CS01-TOFF023-CSd01 = run b0
  where
  b0 : Chain (X3 ∷ CK32 ∷ X3 ∷ Toff023 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ X3 ∷ CK32 ∷ X3 ∷ [])
  b0 = at 0 4 (Toff023 ∷ X3 ∷ CK32 ∷ X3 ∷ []) (lem-pass-X3-CK32-X3-vs-TOFF023) ▸
       at 1 4 (CS01 ∷ X3 ∷ CK32 ∷ X3 ∷ []) (lem-pass-X3-CK32-X3-vs-CS01) ▸
       at 2 4 (Toff023 ∷ X3 ∷ CK32 ∷ X3 ∷ []) (lem-pass-X3-CK32-X3-vs-TOFF023) ▸
       at 3 4 (CS01⁻ ∷ X3 ∷ CK32 ∷ X3 ∷ []) (lem-pass-X3-CK32-X3-vs-CSd01) ▸ done

-- pass [X3 CK31 X3] [CS13 TOFF102 CSd13 TOFF102]: 9 steps
lem-pass-X3-CK31-X3-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (X3 ∷ CK31 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CK31 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CK31-X3-vs-CS13-TOFF102-CSd13-TOFF102 = trans (run b0) (run b1)
  where
  b0 : Chain (X3 ∷ CK31 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CK31 ∷ X3 ∷ Toff102 ∷ Toff102 ∷ [])
  b0 = at 0 0 (CS13 ∷ CS13⁻ ∷ []) wn01376 ▸
       at 1 0 (Toff102 ∷ Toff102 ∷ []) wn01377 ▸
       at 2 0 (CS13⁻ ∷ CS13 ∷ []) wn01378 ▸
       at 3 0 (Toff102 ∷ Toff102 ∷ []) wn01377 ▸
       at 4 7 (X3 ∷ CK31 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (sym lem-pass-X3-CK31-X3-vs-TOFF102-CS13-TOFF102-CSd13) ▸
       at 10 2 [] wn01379 ▸
       at 9 2 [] wn01380 ▸
       at 8 2 [] wn01381 ▸ done

  b1 : Chain (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CK31 ∷ X3 ∷ Toff102 ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CK31 ∷ X3 ∷ [])
  b1 = at 7 2 [] wn01380 ▸ done

-- pass [X3 CS31 X3] [TOFF013 CS02 TOFF013 CSd02]: 4 steps
lem-pass-X3-CS31-X3-vs-TOFF013-CS02-TOFF013-CSd02 : ⟪ (X3 ∷ CS13 ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X3 ∷ CS13 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS31-X3-vs-TOFF013-CS02-TOFF013-CSd02 = run b0
  where
  b0 : Chain (X3 ∷ CS13 ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X3 ∷ CS13 ∷ X3 ∷ [])
  b0 = at 0 4 (Toff013 ∷ X3 ∷ CS13 ∷ X3 ∷ []) (lem-pass-X3-CS31-X3-vs-TOFF013) ▸
       at 1 4 (CS02 ∷ X3 ∷ CS13 ∷ X3 ∷ []) (lem-pass-X3-CS31-X3-vs-CS02) ▸
       at 2 4 (Toff013 ∷ X3 ∷ CS13 ∷ X3 ∷ []) (lem-pass-X3-CS31-X3-vs-TOFF013) ▸
       at 3 4 (CS02⁻ ∷ X3 ∷ CS13 ∷ X3 ∷ []) (lem-pass-X3-CS31-X3-vs-CSd02) ▸ done

-- pass [X3 CK31 X3] [TOFF013 CS02 TOFF013 CSd02]: 4 steps
lem-pass-X3-CK31-X3-vs-TOFF013-CS02-TOFF013-CSd02 : ⟪ (X3 ∷ CK31 ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X3 ∷ CK31 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CK31-X3-vs-TOFF013-CS02-TOFF013-CSd02 = run b0
  where
  b0 : Chain (X3 ∷ CK31 ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X3 ∷ CK31 ∷ X3 ∷ [])
  b0 = at 0 4 (Toff013 ∷ X3 ∷ CK31 ∷ X3 ∷ []) (lem-pass-X3-CK31-X3-vs-TOFF013) ▸
       at 1 4 (CS02 ∷ X3 ∷ CK31 ∷ X3 ∷ []) (lem-pass-X3-CK31-X3-vs-CS02) ▸
       at 2 4 (Toff013 ∷ X3 ∷ CK31 ∷ X3 ∷ []) (lem-pass-X3-CK31-X3-vs-TOFF013) ▸
       at 3 4 (CS02⁻ ∷ X3 ∷ CK31 ∷ X3 ∷ []) (lem-pass-X3-CK31-X3-vs-CSd02) ▸ done

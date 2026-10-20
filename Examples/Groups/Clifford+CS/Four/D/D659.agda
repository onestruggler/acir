{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D659 where

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
open import Examples.Groups.Clifford+CS.Four.Wins.W01 using (wn00001 ; wn00003 ; wn00005 ; wn00007 ; wn00008 ; wn00009 ; wn00010 ; wn00011 ; wn00012 ; wn00014 ; wn00015 ; wn00016 ; wn00020 ; wn00021 ; wn00022 ; wn00023 ; wn00024 ; wn00025 ; wn00026 ; wn00027 ; wn00028 ; wn00029 ; wn00030 ; wn00031 ; wn00032 ; wn00043 ; wn00047 ; wn00048 ; wn00049 ; wn00051 ; wn00127)
open import Examples.Groups.Clifford+CS.Four.Wins.W02 using (wn00253 ; wn00271 ; wn00272 ; wn00333 ; wn00366 ; wn00398)
open import Examples.Groups.Clifford+CS.Four.Wins.W29 using (wn01521)
open import Examples.Groups.Clifford+CS.Four.Wins.W38 using (wn01877)
open import Examples.Groups.Clifford+CS.Four.Wins.W42 using (wn01991 ; wn01992)
open import Examples.Groups.Clifford+CS.Four.D.D378 using (lem-pass-CCZ123-vs-CS23 ; lem-pass-CCZ123-vs-CSd23 ; lem-pass-CZ01-vs-CSd23 ; lem-pass-CZ12-vs-CS23 ; lem-pass-CZ12-vs-CSd23)
open import Examples.Groups.Clifford+CS.Four.D.D514 using (lem-pass-CCZ013-vs-CCZ123)
open import Examples.Groups.Clifford+CS.Four.D.D529 using (lem-pass-CCZ013-vs-CSd23)
open import Examples.Groups.Clifford+CS.Four.D.D642 using (lem-pass-CCZ013-vs-TOFF201)

-- pass [CZ12 CCZ123] [CS23 TOFF201 CSd23 TOFF201]: 806 steps
lem-pass-CZ12-CCZ123-vs-CS23-TOFF201-CSd23-TOFF201 : ⟪ (CZ12 ∷ CCZ123 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ CZ12 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CZ12-CCZ123-vs-CS23-TOFF201-CSd23-TOFF201 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (trans (run b38) (trans (run b39) (trans (run b40) (trans (run b41) (trans (run b42) (trans (run b43) (trans (run b44) (trans (run b45) (trans (run b46) (trans (run b47) (trans (run b48) (trans (run b49) (trans (run b50) (trans (run b51) (trans (run b52) (trans (run b53) (trans (run b54) (trans (run b55) (trans (run b56) (trans (run b57) (trans (run b58) (trans (run b59) (trans (run b60) (trans (run b61) (trans (run b62) (trans (run b63) (trans (run b64) (trans (run b65) (trans (run b66) (trans (run b67) (trans (run b68) (trans (run b69) (trans (run b70) (trans (run b71) (trans (run b72) (trans (run b73) (trans (run b74) (trans (run b75) (trans (run b76) (trans (run b77) (trans (run b78) (trans (run b79) (trans (run b80) (trans (run b81) (trans (run b82) (trans (run b83) (trans (run b84) (trans (run b85) (trans (run b86) (trans (run b87) (trans (run b88) (trans (run b89) (trans (run b90) (trans (run b91) (trans (run b92) (trans (run b93) (trans (run b94) (trans (run b95) (trans (run b96) (trans (run b97) (trans (run b98) (trans (run b99) (run b100))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (CZ12 ∷ CCZ123 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ CZ12 ∷ Toff201 ∷ Toff201 ∷ CCZ123 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw01 ∷ CS12 ∷ K2 ∷ ι1 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ [])
  b0 = at 1 2 (CS23 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-CS23) ▸
       at 0 2 (CS23 ∷ CZ12 ∷ []) (lem-pass-CZ12-vs-CS23) ▸
       at 2 0 (Toff201 ∷ Toff201 ∷ []) wn01521 ▸
       at 6 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 5 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (Sw01 ∷ ι1 ∷ []) wn00127 ▸
       at 11 2 (Sw01 ∷ K2 ∷ []) (sym (low-comm (Swap) (K))) ▸
       at 10 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸ done

  b1 : Chain (CS23 ∷ CZ12 ∷ Toff201 ∷ Toff201 ∷ CCZ123 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw01 ∷ CS12 ∷ K2 ∷ ι1 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ CZ12 ∷ Toff201 ∷ Toff201 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Toff201 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ [])
  b1 = at 9 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 8 2 (Sw01 ∷ CS02⁻ ∷ []) wn00009 ▸
       at 7 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 6 2 (Sw01 ∷ CS02 ∷ []) wn00010 ▸
       at 5 2 (Sw01 ∷ K2 ∷ []) (sym (low-comm (Swap) (K))) ▸
       at 6 8 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) wn00333 ▸
       at 6 8 (Toff201 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (CS23 ∷ CZ12 ∷ Toff201 ∷ Toff201 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Toff201 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ CZ12 ∷ Toff201 ∷ Toff201 ∷ CS23 ∷ Sw01 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Toff201 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ [])
  b2 = at 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 9 2 (Sw01 ∷ CS02 ∷ []) wn00010 ▸
       at 8 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw01 ∷ CX02 ∷ []) wn00253 ▸
       at 6 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 5 2 (Sw01 ∷ CX02 ∷ []) wn00253 ▸ done

  b3 : Chain (CS23 ∷ CZ12 ∷ Toff201 ∷ Toff201 ∷ CS23 ∷ Sw01 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Toff201 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ CZ12 ∷ Toff201 ∷ Toff201 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ Sw01 ∷ CS02 ∷ Sw23 ∷ Toff201 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ [])
  b3 = at 4 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 5 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 6 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 7 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 8 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 9 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b4 : Chain (CS23 ∷ CZ12 ∷ Toff201 ∷ Toff201 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ Sw01 ∷ CS02 ∷ Sw23 ∷ Toff201 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ CZ12 ∷ Toff201 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ Sw01 ∷ ι1 ∷ CCZ023 ∷ Toff201 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ [])
  b4 = at 11 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 12 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸
       at 6 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw01 ∷ ι1 ∷ []) wn00127 ▸ done

  b5 : Chain (CS23 ∷ CZ12 ∷ Toff201 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ Sw01 ∷ ι1 ∷ CCZ023 ∷ Toff201 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ CZ12 ∷ Toff201 ∷ Sw01 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ CCZ023 ∷ Toff201 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ [])
  b5 = at 9 2 (Sw01 ∷ K2 ∷ []) (sym (low-comm (Swap) (K))) ▸
       at 8 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 7 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 6 2 (Sw01 ∷ CS02⁻ ∷ []) wn00009 ▸
       at 5 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 4 2 (Sw01 ∷ CS02 ∷ []) wn00010 ▸
       at 3 2 (Sw01 ∷ K2 ∷ []) (sym (low-comm (Swap) (K))) ▸
       at 4 8 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) wn00333 ▸ done

  b6 : Chain (CS23 ∷ CZ12 ∷ Toff201 ∷ Sw01 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ CCZ023 ∷ Toff201 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ CZ12 ∷ Toff201 ∷ Sw01 ∷ Toff201 ∷ CCZ023 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw12 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ CS01 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ [])
  b6 = at 4 8 (Toff201 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 6 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (Sw12 ∷ ι ∷ []) (low₁-comm (iI) (Swap)) ▸
       at 12 2 (Sw12 ∷ K1 ∷ []) wn00398 ▸
       at 11 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 [] wn00014 ▸
       at 10 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸ done

  b7 : Chain (CS23 ∷ CZ12 ∷ Toff201 ∷ Sw01 ∷ Toff201 ∷ CCZ023 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw12 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ CS01 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ CZ12 ∷ Toff201 ∷ Sw01 ∷ Toff201 ∷ CCZ023 ∷ Sw12 ∷ Toff102 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ [])
  b7 = at 11 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw12 ∷ CS12⁻ ∷ []) wn00015 ▸
       at 8 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 9 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw12 ∷ CS12 ∷ []) wn00016 ▸
       at 6 2 (Sw12 ∷ K1 ∷ []) wn00398 ▸
       at 7 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) wn00366 ▸
       at 7 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸ done

  b8 : Chain (CS23 ∷ CZ12 ∷ Toff201 ∷ Sw01 ∷ Toff201 ∷ CCZ023 ∷ Sw12 ∷ Toff102 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ CZ12 ∷ Toff201 ∷ Sw01 ∷ Toff201 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Toff102 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ [])
  b8 = at 5 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 6 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 7 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 8 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b9 : Chain (CS23 ∷ CZ12 ∷ Toff201 ∷ Sw01 ∷ Toff201 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Toff102 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ CZ12 ∷ Toff201 ∷ Sw01 ∷ Toff201 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Toff102 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ [])
  b9 = at 10 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00031 ▸
       at 9 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) wn00022 ▸
       at 11 2 (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap)) ▸
       at 9 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) wn00023 ▸ done

  b10 : Chain (CS23 ∷ CZ12 ∷ Toff201 ∷ Sw01 ∷ Toff201 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Toff102 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ CZ12 ∷ Toff201 ∷ Sw01 ∷ Toff201 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Toff102 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ [])
  b10 = at 10 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00014 ▸
       at 7 2 (Sw12 ∷ CS13⁻ ∷ []) wn00047 ▸
       at 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00014 ▸
       at 5 2 (Sw12 ∷ CS13 ∷ []) wn00048 ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b11 : Chain (CS23 ∷ CZ12 ∷ Toff201 ∷ Sw01 ∷ Toff201 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Toff102 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ CZ12 ∷ Toff201 ∷ Sw01 ∷ Toff201 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Toff102 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ [])
  b11 = at 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00003 ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00003 ▸
       at 10 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] wn00003 ▸ done

  b12 : Chain (CS23 ∷ CZ12 ∷ Toff201 ∷ Sw01 ∷ Toff201 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Toff102 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ CZ12 ∷ Toff201 ∷ Sw01 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw12 ∷ CS01 ∷ K1 ∷ ι ∷ CCZ013 ∷ Toff102 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ [])
  b12 = at 7 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00043 ▸
       at 7 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 6 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (Sw12 ∷ ι ∷ []) (low₁-comm (iI) (Swap)) ▸
       at 10 2 (Sw12 ∷ K1 ∷ []) wn00398 ▸
       at 9 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] wn00014 ▸ done

  b13 : Chain (CS23 ∷ CZ12 ∷ Toff201 ∷ Sw01 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw12 ∷ CS01 ∷ K1 ∷ ι ∷ CCZ013 ∷ Toff102 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ CCZ013 ∷ Toff102 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ [])
  b13 = at 8 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 9 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw12 ∷ CS12⁻ ∷ []) wn00015 ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 7 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw12 ∷ CS12 ∷ []) wn00016 ▸
       at 4 2 (Sw12 ∷ K1 ∷ []) wn00398 ▸
       at 5 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) wn00366 ▸ done

  b14 : Chain (CS23 ∷ CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ CCZ013 ∷ Toff102 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Toff102 ∷ CCZ013 ∷ K1 ∷ CS12 ∷ CX01 ∷ Sw01 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K0 ∷ ι1 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ [])
  b14 = at 5 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 7 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 (Sw01 ∷ ι1 ∷ []) wn00127 ▸
       at 13 2 (Sw01 ∷ K0 ∷ []) wn00271 ▸
       at 12 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 11 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 10 2 (Sw01 ∷ CS02⁻ ∷ []) wn00009 ▸ done

  b15 : Chain (CS23 ∷ CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Toff102 ∷ CCZ013 ∷ K1 ∷ CS12 ∷ CX01 ∷ Sw01 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K0 ∷ ι1 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Toff102 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ [])
  b15 = at 9 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 8 2 (Sw01 ∷ CS02 ∷ []) wn00010 ▸
       at 7 2 (Sw01 ∷ K0 ∷ []) wn00271 ▸
       at 8 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) wn00272 ▸
       at 8 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b16 : Chain (CS23 ∷ CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Toff102 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Toff102 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw01 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ [])
  b16 = at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 8 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 10 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] wn00003 ▸ done

  b17 : Chain (CS23 ∷ CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Toff102 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw01 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Toff102 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw01 ∷ Sw23 ∷ CX10 ∷ CS13 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ [])
  b17 = at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 11 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 10 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 11 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b18 : Chain (CS23 ∷ CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Toff102 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw01 ∷ Sw23 ∷ CX10 ∷ CS13 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Toff102 ∷ Sw01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ [])
  b18 = at 9 2 (Sw01 ∷ CS02⁻ ∷ []) wn00009 ▸
       at 8 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 9 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 7 2 (Sw01 ∷ CS02 ∷ []) wn00010 ▸
       at 6 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b19 : Chain (CS23 ∷ CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Toff102 ∷ Sw01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Toff102 ∷ Sw01 ∷ Sw23 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ Sw23 ∷ CS13 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ [])
  b19 = at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00003 ▸
       at 9 2 (CX10 ∷ Sw23 ∷ []) (sym (low-comm (CX₁₀) (Swap))) ▸
       at 11 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00003 ▸
       at 11 2 (CX10 ∷ Sw23 ∷ []) (sym (low-comm (CX₁₀) (Swap))) ▸ done

  b20 : Chain (CS23 ∷ CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Toff102 ∷ Sw01 ∷ Sw23 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ Sw23 ∷ CS13 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw01 ∷ K0 ∷ ι1 ∷ CCZ013 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ [])
  b20 = at 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] wn00003 ▸
       at 8 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00011 ▸
       at 8 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 7 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (Sw01 ∷ ι1 ∷ []) wn00127 ▸
       at 11 2 (Sw01 ∷ K0 ∷ []) wn00271 ▸ done

  b21 : Chain (CS23 ∷ CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw01 ∷ K0 ∷ ι1 ∷ CCZ013 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Toff012 ∷ CCZ013 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ [])
  b21 = at 10 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 9 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 8 2 (Sw01 ∷ CS02⁻ ∷ []) wn00009 ▸
       at 7 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 6 2 (Sw01 ∷ CS02 ∷ []) wn00010 ▸
       at 5 2 (Sw01 ∷ K0 ∷ []) wn00271 ▸
       at 6 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) wn00272 ▸
       at 6 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸ done

  b22 : Chain (CS23 ∷ CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Toff012 ∷ CCZ013 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ [])
  b22 = at 6 3 (CCZ013 ∷ CCZ123 ∷ []) (ax toff-ccz) ▸
       at 6 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 8 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b23 : Chain (CS23 ∷ CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ [])
  b23 = at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 10 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] wn00003 ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b24 : Chain (CS23 ∷ CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ Sw01 ∷ CS03 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ [])
  b24 = at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX10 ∷ Sw01 ∷ []) wn00028 ▸
       at 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX10 ∷ Sw01 ∷ []) wn00028 ▸ done

  b25 : Chain (CS23 ∷ CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ Sw01 ∷ CS03 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ [])
  b25 = at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸ done

  b26 : Chain (CS23 ∷ CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ [])
  b26 = at 7 2 (CX10 ∷ Sw23 ∷ []) (sym (low-comm (CX₁₀) (Swap))) ▸
       at 9 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00003 ▸
       at 9 2 (CX10 ∷ Sw23 ∷ []) (sym (low-comm (CX₁₀) (Swap))) ▸
       at 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00003 ▸
       at 6 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00011 ▸
       at 6 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸ done

  b27 : Chain (CS23 ∷ CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ CCZ013 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ [])
  b27 = at 5 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 7 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 8 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 9 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b28 : Chain (CS23 ∷ CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ CCZ013 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ CCZ013 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw01 ∷ CS03 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ [])
  b28 = at 11 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 12 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 7 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 8 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 9 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 10 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸ done

  b29 : Chain (CS23 ∷ CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ CCZ013 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw01 ∷ CS03 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ CCZ013 ∷ CCZ023 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ [])
  b29 = at 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 12 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 13 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 11 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸
       at 7 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 6 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸ done

  b30 : Chain (CS23 ∷ CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ CCZ013 ∷ CCZ023 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ CCZ023 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ [])
  b30 = at 7 2 [] wn00031 ▸
       at 5 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 7 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b31 : Chain (CS23 ∷ CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ CCZ023 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ CZ12 ∷ Toff201 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw12 ∷ CX01 ∷ CS03 ∷ CCZ023 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ [])
  b31 = at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00003 ▸
       at 4 2 (CS23 ∷ Sw12 ∷ []) wn00020 ▸
       at 7 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 5 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS23⁻ ∷ Sw12 ∷ []) wn00021 ▸ done

  b32 : Chain (CS23 ∷ CZ12 ∷ Toff201 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw12 ∷ CX01 ∷ CS03 ∷ CCZ023 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw12 ∷ CCZ023 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ [])
  b32 = at 9 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 7 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 9 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) wn00022 ▸
       at 10 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 11 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) wn00023 ▸
       at 8 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 4 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸ done

  b33 : Chain (CS23 ∷ CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw12 ∷ CCZ023 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ CCZ023 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ [])
  b33 = at 5 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 6 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 7 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 8 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b34 : Chain (CS23 ∷ CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ CCZ023 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ CZ12 ∷ Toff201 ∷ Sw01 ∷ CCZ023 ∷ Sw12 ∷ CS23 ∷ CX02 ∷ Sw01 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ [])
  b34 = at 9 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸
       at 5 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 4 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 7 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸ done

  b35 : Chain (CS23 ∷ CZ12 ∷ Toff201 ∷ Sw01 ∷ CCZ023 ∷ Sw12 ∷ CS23 ∷ CX02 ∷ Sw01 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ CZ12 ∷ Toff201 ∷ Sw01 ∷ CCZ023 ∷ Sw12 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ [])
  b35 = at 8 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 9 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 11 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 12 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] wn00031 ▸ done

  b36 : Chain (CS23 ∷ CZ12 ∷ Toff201 ∷ Sw01 ∷ CCZ023 ∷ Sw12 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ CZ12 ∷ Toff201 ∷ Sw01 ∷ CCZ023 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ [])
  b36 = at 5 2 (CS13 ∷ Sw12 ∷ []) wn00049 ▸
       at 7 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00014 ▸
       at 7 2 (CS13⁻ ∷ Sw12 ∷ []) wn00051 ▸
       at 9 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00014 ▸
       at 10 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) wn00022 ▸ done

  b37 : Chain (CS23 ∷ CZ12 ∷ Toff201 ∷ Sw01 ∷ CCZ023 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ CZ12 ∷ Toff201 ∷ Sw01 ∷ CCZ023 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ Sw23 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ Sw12 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ [])
  b37 = at 11 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 12 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) wn00023 ▸
       at 9 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b38 : Chain (CS23 ∷ CZ12 ∷ Toff201 ∷ Sw01 ∷ CCZ023 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ Sw23 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ Sw12 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ CZ12 ∷ Toff201 ∷ Sw01 ∷ CCZ023 ∷ CCZ013 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ [])
  b38 = at 8 2 [] wn00003 ▸
       at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00003 ▸
       at 6 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00043 ▸
       at 6 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00014 ▸ done

  b39 : Chain (CS23 ∷ CZ12 ∷ Toff201 ∷ Sw01 ∷ CCZ023 ∷ CCZ013 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ CZ12 ∷ Toff201 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ CCZ013 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ [])
  b39 = at 4 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 5 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 6 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 7 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b40 : Chain (CS23 ∷ CZ12 ∷ Toff201 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ CCZ013 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ CZ12 ∷ Toff201 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw01 ∷ CS03 ∷ CCZ013 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ [])
  b40 = at 9 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00031 ▸
       at 3 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 4 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 5 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 6 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸ done

  b41 : Chain (CS23 ∷ CZ12 ∷ Toff201 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw01 ∷ CS03 ∷ CCZ013 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ CZ12 ∷ Toff201 ∷ CCZ123 ∷ Sw01 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ [])
  b41 = at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸
       at 3 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b42 : Chain (CS23 ∷ CZ12 ∷ Toff201 ∷ CCZ123 ∷ Sw01 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ CZ12 ∷ Toff201 ∷ CCZ123 ∷ Sw01 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ [])
  b42 = at 6 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 7 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b43 : Chain (CS23 ∷ CZ12 ∷ Toff201 ∷ CCZ123 ∷ Sw01 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ CZ12 ∷ Toff201 ∷ CCZ123 ∷ CS03 ∷ CX10 ∷ Sw01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ [])
  b43 = at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00003 ▸
       at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 4 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX10 ∷ Sw01 ∷ []) wn00028 ▸ done

  b44 : Chain (CS23 ∷ CZ12 ∷ Toff201 ∷ CCZ123 ∷ CS03 ∷ CX10 ∷ Sw01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ CZ12 ∷ Toff201 ∷ CCZ123 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ Sw23 ∷ Sw01 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ [])
  b44 = at 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX10 ∷ Sw01 ∷ []) wn00028 ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b45 : Chain (CS23 ∷ CZ12 ∷ Toff201 ∷ CCZ123 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ Sw23 ∷ Sw01 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ CZ12 ∷ Toff201 ∷ CCZ123 ∷ Sw23 ∷ CS02 ∷ CX10 ∷ Sw23 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ CX10 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ [])
  b45 = at 9 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 6 2 (CX10 ∷ Sw23 ∷ []) (sym (low-comm (CX₁₀) (Swap))) ▸
       at 8 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b46 : Chain (CS23 ∷ CZ12 ∷ Toff201 ∷ CCZ123 ∷ Sw23 ∷ CS02 ∷ CX10 ∷ Sw23 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ CX10 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ CZ12 ∷ Toff201 ∷ CCZ123 ∷ CCZ013 ∷ CS23⁻ ∷ Toff201 ∷ [])
  b46 = at 7 2 [] wn00003 ▸
       at 8 2 (CX10 ∷ Sw23 ∷ []) (sym (low-comm (CX₁₀) (Swap))) ▸
       at 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00003 ▸
       at 5 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00011 ▸
       at 5 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 4 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00031 ▸ done

  b47 : Chain (CS23 ∷ CZ12 ∷ Toff201 ∷ CCZ123 ∷ CCZ013 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Toff201 ∷ CCZ123 ∷ Toff201 ∷ Sw01 ∷ Sw01 ∷ [])
  b47 = at 1 2 (Toff201 ∷ CZ01 ∷ CZ12 ∷ []) wn01991 ▸
       at 4 2 (CCZ013 ∷ CCZ123 ∷ []) (sym lem-pass-CCZ013-vs-CCZ123) ▸
       at 5 2 (CS23⁻ ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-CSd23) ▸
       at 4 2 (CS23⁻ ∷ CCZ013 ∷ []) (lem-pass-CCZ013-vs-CSd23) ▸
       at 3 2 (CS23⁻ ∷ CZ12 ∷ []) (lem-pass-CZ12-vs-CSd23) ▸
       at 2 2 (CS23⁻ ∷ CZ01 ∷ []) (lem-pass-CZ01-vs-CSd23) ▸
       at 6 0 (Toff201 ∷ Toff201 ∷ []) wn01521 ▸
       at 10 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸ done

  b48 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Toff201 ∷ CCZ123 ∷ Toff201 ∷ Sw01 ∷ Sw01 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Toff201 ∷ CCZ123 ∷ K2 ∷ Sw01 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K2 ∷ ι1 ∷ Sw01 ∷ [])
  b48 = at 9 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 16 2 (Sw01 ∷ ι1 ∷ []) wn00127 ▸
       at 15 2 (Sw01 ∷ K2 ∷ []) (sym (low-comm (Swap) (K))) ▸
       at 14 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 13 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 12 2 (Sw01 ∷ CS02⁻ ∷ []) wn00009 ▸
       at 11 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 10 2 (Sw01 ∷ CS02 ∷ []) wn00010 ▸ done

  b49 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Toff201 ∷ CCZ123 ∷ K2 ∷ Sw01 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K2 ∷ ι1 ∷ Sw01 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Toff201 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Toff201 ∷ Sw01 ∷ [])
  b49 = at 9 2 (Sw01 ∷ K2 ∷ []) (sym (low-comm (Swap) (K))) ▸
       at 10 8 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) wn00333 ▸
       at 10 8 (Toff201 ∷ []) (by-assoc Eq.refl) ▸
       at 8 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 13 2 (Sw01 ∷ CS02 ∷ []) wn00010 ▸
       at 12 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b50 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Toff201 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Toff201 ∷ Sw01 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Toff201 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ Sw01 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Toff201 ∷ Sw01 ∷ [])
  b50 = at 13 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (Sw01 ∷ CX02 ∷ []) wn00253 ▸
       at 10 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 9 2 (Sw01 ∷ CX02 ∷ []) wn00253 ▸
       at 8 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 9 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 10 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 11 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸ done

  b51 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Toff201 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ Sw01 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Toff201 ∷ Sw01 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Toff201 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Toff201 ∷ Sw01 ∷ [])
  b51 = at 12 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 13 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 15 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 16 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 14 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 10 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸ done

  b52 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Toff201 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Toff201 ∷ Sw01 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ K2 ∷ CS12 ∷ CX01 ∷ Sw01 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K2 ∷ ι1 ∷ CCZ023 ∷ Toff201 ∷ Sw01 ∷ [])
  b52 = at 10 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 9 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 (Sw01 ∷ ι1 ∷ []) wn00127 ▸
       at 13 2 (Sw01 ∷ K2 ∷ []) (sym (low-comm (Swap) (K))) ▸
       at 12 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 11 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 10 2 (Sw01 ∷ CS02⁻ ∷ []) wn00009 ▸ done

  b53 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ K2 ∷ CS12 ∷ CX01 ∷ Sw01 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K2 ∷ ι1 ∷ CCZ023 ∷ Toff201 ∷ Sw01 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Toff201 ∷ CCZ023 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ Sw12 ∷ ι ∷ Sw12 ∷ Sw01 ∷ [])
  b53 = at 9 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 8 2 (Sw01 ∷ CS02 ∷ []) wn00010 ▸
       at 7 2 (Sw01 ∷ K2 ∷ []) (sym (low-comm (Swap) (K))) ▸
       at 8 8 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) wn00333 ▸
       at 8 8 (Toff201 ∷ []) (by-assoc Eq.refl) ▸
       at 11 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 10 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 17 2 (Sw12 ∷ ι ∷ []) (low₁-comm (iI) (Swap)) ▸ done

  b54 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Toff201 ∷ CCZ023 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ Sw12 ∷ ι ∷ Sw12 ∷ Sw01 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Toff201 ∷ CCZ023 ∷ K2 ∷ CS12 ∷ Sw12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw01 ∷ [])
  b54 = at 16 2 (Sw12 ∷ K1 ∷ []) wn00398 ▸
       at 15 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 17 2 [] wn00014 ▸
       at 14 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 15 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (Sw12 ∷ CS12⁻ ∷ []) wn00015 ▸
       at 12 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 13 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸ done

  b55 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Toff201 ∷ CCZ023 ∷ K2 ∷ CS12 ∷ Sw12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw01 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Toff201 ∷ CS23 ∷ CX02 ∷ Sw01 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw12 ∷ Toff102 ∷ Sw12 ∷ Sw01 ∷ [])
  b55 = at 11 2 (Sw12 ∷ CS12 ∷ []) wn00016 ▸
       at 10 2 (Sw12 ∷ K1 ∷ []) wn00398 ▸
       at 11 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) wn00366 ▸
       at 11 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 9 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 10 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 10 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸ done

  b56 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Toff201 ∷ CS23 ∷ CX02 ∷ Sw01 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw12 ∷ Toff102 ∷ Sw12 ∷ Sw01 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Toff201 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw12 ∷ Toff102 ∷ Sw12 ∷ Sw01 ∷ [])
  b56 = at 11 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 12 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 14 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 14 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 15 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 13 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 [] wn00031 ▸ done

  b57 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Toff201 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw12 ∷ Toff102 ∷ Sw12 ∷ Sw01 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Toff201 ∷ CS23 ∷ CX02 ∷ Sw12 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Toff102 ∷ Sw12 ∷ Sw01 ∷ [])
  b57 = at 13 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 16 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) wn00022 ▸
       at 15 2 (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap)) ▸
       at 13 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) wn00023 ▸
       at 14 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 12 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 [] wn00014 ▸
       at 11 2 (Sw12 ∷ CS13⁻ ∷ []) wn00047 ▸ done

  b58 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Toff201 ∷ CS23 ∷ CX02 ∷ Sw12 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Toff102 ∷ Sw12 ∷ Sw01 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Toff201 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ Sw23 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ Toff102 ∷ Sw12 ∷ Sw01 ∷ [])
  b58 = at 10 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] wn00014 ▸
       at 9 2 (Sw12 ∷ CS13 ∷ []) wn00048 ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] wn00003 ▸
       at 12 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 14 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b59 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Toff201 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ Sw23 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ Toff102 ∷ Sw12 ∷ Sw01 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw12 ∷ CCZ013 ∷ Toff102 ∷ Sw12 ∷ Sw01 ∷ [])
  b59 = at 13 2 [] wn00003 ▸
       at 14 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 [] wn00003 ▸
       at 11 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00043 ▸
       at 11 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 10 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 8 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸ done

  b60 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw12 ∷ CCZ013 ∷ Toff102 ∷ Sw12 ∷ Sw01 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ K2 ∷ CS12 ∷ Sw12 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K1 ∷ ι ∷ CCZ013 ∷ Toff102 ∷ Sw12 ∷ Sw01 ∷ [])
  b60 = at 15 2 (Sw12 ∷ ι ∷ []) (low₁-comm (iI) (Swap)) ▸
       at 14 2 (Sw12 ∷ K1 ∷ []) wn00398 ▸
       at 13 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 [] wn00014 ▸
       at 12 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 13 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (Sw12 ∷ CS12⁻ ∷ []) wn00015 ▸
       at 10 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸ done

  b61 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ K2 ∷ CS12 ∷ Sw12 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K1 ∷ ι ∷ CCZ013 ∷ Toff102 ∷ Sw12 ∷ Sw01 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Toff102 ∷ CCZ013 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ Sw01 ∷ ι1 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b61 = at 11 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw12 ∷ CS12 ∷ []) wn00016 ▸
       at 8 2 (Sw12 ∷ K1 ∷ []) wn00398 ▸
       at 9 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) wn00366 ▸
       at 9 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 12 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 11 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 18 2 (Sw01 ∷ ι1 ∷ []) wn00127 ▸ done

  b62 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Toff102 ∷ CCZ013 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ Sw01 ∷ ι1 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Toff102 ∷ CCZ013 ∷ Sw01 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b62 = at 17 2 (Sw01 ∷ K0 ∷ []) wn00271 ▸
       at 16 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 15 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 14 2 (Sw01 ∷ CS02⁻ ∷ []) wn00009 ▸
       at 13 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 12 2 (Sw01 ∷ CS02 ∷ []) wn00010 ▸
       at 11 2 (Sw01 ∷ K0 ∷ []) wn00271 ▸
       at 12 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) wn00272 ▸ done

  b63 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Toff102 ∷ CCZ013 ∷ Sw01 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Toff102 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b63 = at 12 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 10 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 10 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 14 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 12 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b64 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Toff102 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Toff102 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b64 = at 13 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 16 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 14 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 [] wn00003 ▸
       at 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 16 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 15 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 14 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b65 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Toff102 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Toff102 ∷ CS13 ∷ Sw01 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b65 = at 15 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 12 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 13 2 (Sw01 ∷ CS02⁻ ∷ []) wn00009 ▸
       at 12 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 13 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸ done

  b66 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Toff102 ∷ CS13 ∷ Sw01 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Toff102 ∷ Sw01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b66 = at 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 11 2 (Sw01 ∷ CS02 ∷ []) wn00010 ▸
       at 10 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 11 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] wn00003 ▸ done

  b67 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Toff102 ∷ Sw01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Toff102 ∷ Sw01 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b67 = at 13 2 (CX10 ∷ Sw23 ∷ []) (sym (low-comm (CX₁₀) (Swap))) ▸
       at 15 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 [] wn00003 ▸
       at 15 2 (CX10 ∷ Sw23 ∷ []) (sym (low-comm (CX₁₀) (Swap))) ▸
       at 17 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 16 2 [] wn00003 ▸
       at 12 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00011 ▸
       at 12 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸ done

  b68 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Toff102 ∷ Sw01 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ K1 ∷ CS12 ∷ Sw01 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K0 ∷ ι1 ∷ CCZ013 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b68 = at 11 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 9 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 16 2 (Sw01 ∷ ι1 ∷ []) wn00127 ▸
       at 15 2 (Sw01 ∷ K0 ∷ []) wn00271 ▸
       at 14 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 13 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 12 2 (Sw01 ∷ CS02⁻ ∷ []) wn00009 ▸
       at 11 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸ done

  b69 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ K1 ∷ CS12 ∷ Sw01 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K0 ∷ ι1 ∷ CCZ013 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b69 = at 10 2 (Sw01 ∷ CS02 ∷ []) wn00010 ▸
       at 9 2 (Sw01 ∷ K0 ∷ []) wn00271 ▸
       at 10 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) wn00272 ▸
       at 10 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 10 3 (CCZ013 ∷ CCZ123 ∷ []) (ax toff-ccz) ▸
       at 10 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b70 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b70 = at 10 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 14 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 12 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 16 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 14 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 [] wn00003 ▸ done

  b71 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ CS03 ∷ CX10 ∷ Sw23 ∷ Sw01 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b71 = at 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (CX10 ∷ Sw01 ∷ []) wn00028 ▸
       at 12 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b72 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ CS03 ∷ CX10 ∷ Sw23 ∷ Sw01 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b72 = at 12 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸
       at 13 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 11 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (CX10 ∷ Sw01 ∷ []) wn00028 ▸
       at 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 14 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 15 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b73 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ Sw23 ∷ CS13 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b73 = at 13 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00003 ▸
       at 11 2 (CX10 ∷ Sw23 ∷ []) (sym (low-comm (CX₁₀) (Swap))) ▸
       at 13 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] wn00003 ▸
       at 13 2 (CX10 ∷ Sw23 ∷ []) (sym (low-comm (CX₁₀) (Swap))) ▸ done

  b74 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ Sw23 ∷ CS13 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ CCZ013 ∷ CS23 ∷ CX02 ∷ Sw01 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b74 = at 15 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 [] wn00003 ▸
       at 10 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00011 ▸
       at 10 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 9 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 11 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 11 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸ done

  b75 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ CCZ013 ∷ CS23 ∷ CX02 ∷ Sw01 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ CCZ013 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b75 = at 12 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 13 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 15 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 15 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 16 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 14 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸ done

  b76 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ CCZ013 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ CCZ013 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b76 = at 11 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 12 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 13 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 14 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 16 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 17 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b77 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ CCZ013 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ CCZ023 ∷ Sw12 ∷ Sw01 ∷ [])
  b77 = at 15 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 11 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸
       at 11 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 10 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] wn00031 ▸
       at 9 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b78 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ CCZ023 ∷ Sw12 ∷ Sw01 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ CCZ023 ∷ Sw12 ∷ Sw01 ∷ [])
  b78 = at 9 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 13 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 11 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 15 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 13 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 [] wn00003 ▸ done

  b79 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ CCZ023 ∷ Sw12 ∷ Sw01 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ CCZ023 ∷ Sw12 ∷ Sw01 ∷ [])
  b79 = at 8 2 (CS23 ∷ Sw12 ∷ []) wn00020 ▸
       at 11 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 9 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (CS23⁻ ∷ Sw12 ∷ []) wn00021 ▸
       at 13 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 11 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 13 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) wn00022 ▸ done

  b80 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ CCZ023 ∷ Sw12 ∷ Sw01 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw01 ∷ CS03 ∷ Sw12 ∷ CCZ023 ∷ Sw12 ∷ Sw01 ∷ [])
  b80 = at 14 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 15 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) wn00023 ▸
       at 12 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 9 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 10 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 11 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 12 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸ done

  b81 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw01 ∷ CS03 ∷ Sw12 ∷ CCZ023 ∷ Sw12 ∷ Sw01 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ CCZ023 ∷ Sw12 ∷ CCZ023 ∷ Sw12 ∷ Sw01 ∷ [])
  b81 = at 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 14 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 15 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 13 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 9 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸
       at 9 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 8 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸ done

  b82 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ CCZ023 ∷ Sw12 ∷ CCZ023 ∷ Sw12 ∷ Sw01 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ CCZ023 ∷ Sw12 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b82 = at 10 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 11 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 11 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 12 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 13 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 15 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b83 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ CCZ023 ∷ Sw12 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ CCZ023 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw12 ∷ CX02 ∷ CS03 ∷ Sw12 ∷ Sw01 ∷ [])
  b83 = at 15 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 16 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 14 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 [] wn00031 ▸
       at 9 2 (CS13 ∷ Sw12 ∷ []) wn00049 ▸
       at 11 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00014 ▸
       at 11 2 (CS13⁻ ∷ Sw12 ∷ []) wn00051 ▸ done

  b84 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ CCZ023 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw12 ∷ CX02 ∷ CS03 ∷ Sw12 ∷ Sw01 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ CCZ023 ∷ Sw23 ∷ Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw12 ∷ Sw12 ∷ Sw01 ∷ [])
  b84 = at 13 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] wn00014 ▸
       at 14 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) wn00022 ▸
       at 15 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 16 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) wn00023 ▸
       at 13 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b85 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ CCZ023 ∷ Sw23 ∷ Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw12 ∷ Sw12 ∷ Sw01 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ CCZ023 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw01 ∷ [])
  b85 = at 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00003 ▸
       at 11 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 13 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] wn00003 ▸
       at 13 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 [] wn00003 ▸ done

  b86 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ CCZ023 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw01 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ Sw01 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ CCZ013 ∷ Sw01 ∷ [])
  b86 = at 10 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00043 ▸
       at 10 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 9 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00014 ▸
       at 8 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 9 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 9 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸ done

  b87 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ Sw01 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ CCZ013 ∷ Sw01 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ CCZ013 ∷ Sw01 ∷ [])
  b87 = at 10 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 11 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 13 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 14 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 12 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 [] wn00031 ▸ done

  b88 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ CCZ013 ∷ Sw01 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ CCZ013 ∷ Sw01 ∷ [])
  b88 = at 7 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 8 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 9 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 10 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 12 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 13 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b89 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ CCZ013 ∷ Sw01 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ CCZ123 ∷ Sw01 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ [])
  b89 = at 11 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸
       at 7 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 9 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 9 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b90 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ CCZ123 ∷ Sw01 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ CCZ123 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw01 ∷ [])
  b90 = at 13 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 11 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 15 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 13 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 [] wn00003 ▸
       at 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b91 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ CCZ123 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw01 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ CCZ123 ∷ CS03 ∷ CX10 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Sw01 ∷ CX01 ∷ CS03 ∷ Sw01 ∷ [])
  b91 = at 9 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CX10 ∷ Sw01 ∷ []) wn00028 ▸
       at 11 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 11 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸
       at 12 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b92 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ CCZ123 ∷ CS03 ∷ CX10 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Sw01 ∷ CX01 ∷ CS03 ∷ Sw01 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ CCZ123 ∷ Sw23 ∷ Sw23 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ [])
  b92 = at 10 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (CX10 ∷ Sw01 ∷ []) wn00028 ▸
       at 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 13 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 14 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 12 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b93 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ CCZ123 ∷ Sw23 ∷ Sw23 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ CCZ123 ∷ Sw23 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ [])
  b93 = at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00003 ▸
       at 10 2 (CX10 ∷ Sw23 ∷ []) (sym (low-comm (CX₁₀) (Swap))) ▸
       at 12 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] wn00003 ▸
       at 12 2 (CX10 ∷ Sw23 ∷ []) (sym (low-comm (CX₁₀) (Swap))) ▸
       at 14 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 [] wn00003 ▸ done

  b94 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ CCZ123 ∷ Sw23 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ CZ01 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ CCZ013 ∷ CCZ123 ∷ [])
  b94 = at 9 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00011 ▸
       at 9 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 8 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00031 ▸
       at 5 2 (Toff201 ∷ CCZ013 ∷ []) (lem-pass-CCZ013-vs-TOFF201) ▸
       at 4 2 (Toff201 ∷ CZ01 ∷ CZ12 ∷ []) wn01991 ▸
       at 3 2 (Toff201 ∷ CZ01 ∷ []) wn01992 ▸
       at 8 2 (CCZ013 ∷ CCZ123 ∷ []) (sym lem-pass-CCZ013-vs-CCZ123) ▸ done

  b95 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ CZ01 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ CCZ013 ∷ CCZ123 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ CZ12 ∷ CCZ013 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CCZ123 ∷ [])
  b95 = at 4 2 [] wn01877 ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b96 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ CZ12 ∷ CCZ013 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CCZ123 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ CZ12 ∷ CCZ013 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ CCZ123 ∷ [])
  b96 = at 8 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 10 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] wn00003 ▸
       at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] wn00003 ▸
       at 9 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸ done

  b97 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ CZ12 ∷ CCZ013 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ CCZ123 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ CZ12 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ CCZ123 ∷ [])
  b97 = at 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00003 ▸
       at 7 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00003 ▸
       at 7 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00043 ▸
       at 7 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b98 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ CZ12 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ CCZ123 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ CZ12 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ CCZ123 ∷ [])
  b98 = at 6 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 7 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b99 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ CZ12 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ CCZ123 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ CZ12 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ CCZ012 ∷ Sw23 ∷ CCZ123 ∷ [])
  b99 = at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00003 ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] wn00003 ▸
       at 8 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00003 ▸
       at 6 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸ done

  b100 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ CZ12 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ CCZ012 ∷ Sw23 ∷ CCZ123 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ CZ12 ∷ CCZ123 ∷ [])
  b100 = at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00003 ▸
       at 6 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00043 ▸
       at 6 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00032 ▸
       at 5 2 [] wn00003 ▸ done

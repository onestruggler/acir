{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D662 where

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
open import Examples.Groups.Clifford+CS.Four.D.D378 using (lem-pass-CCZ123-vs-CS23 ; lem-pass-CCZ123-vs-CSd23 ; lem-pass-CZ12-vs-CS23 ; lem-pass-CZ12-vs-CSd23)
open import Examples.Groups.Clifford+CS.Four.D.D387 using (lem-pass-CZ01-vs-CS23)
open import Examples.Groups.Clifford+CS.Four.D.D513 using (lem-pass-CCZ013-vs-CS23)
open import Examples.Groups.Clifford+CS.Four.D.D514 using (lem-pass-CCZ013-vs-CCZ123)
open import Examples.Groups.Clifford+CS.Four.D.D642 using (lem-pass-CCZ013-vs-TOFF201)

-- pass [CZ12 CCZ123] [TOFF201 CS23 TOFF201 CSd23]: 806 steps
lem-pass-CZ12-CCZ123-vs-TOFF201-CS23-TOFF201-CSd23 : ⟪ (CZ12 ∷ CCZ123 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ12 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CZ12-CCZ123-vs-TOFF201-CS23-TOFF201-CSd23 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (trans (run b38) (trans (run b39) (trans (run b40) (trans (run b41) (trans (run b42) (trans (run b43) (trans (run b44) (trans (run b45) (trans (run b46) (trans (run b47) (trans (run b48) (trans (run b49) (trans (run b50) (trans (run b51) (trans (run b52) (trans (run b53) (trans (run b54) (trans (run b55) (trans (run b56) (trans (run b57) (trans (run b58) (trans (run b59) (trans (run b60) (trans (run b61) (trans (run b62) (trans (run b63) (trans (run b64) (trans (run b65) (trans (run b66) (trans (run b67) (trans (run b68) (trans (run b69) (trans (run b70) (trans (run b71) (trans (run b72) (trans (run b73) (trans (run b74) (trans (run b75) (trans (run b76) (trans (run b77) (trans (run b78) (trans (run b79) (trans (run b80) (trans (run b81) (trans (run b82) (trans (run b83) (trans (run b84) (trans (run b85) (trans (run b86) (trans (run b87) (trans (run b88) (trans (run b89) (trans (run b90) (trans (run b91) (trans (run b92) (trans (run b93) (trans (run b94) (trans (run b95) (trans (run b96) (trans (run b97) (trans (run b98) (trans (run b99) (run b100))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (CZ12 ∷ CCZ123 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (CZ12 ∷ Toff201 ∷ Toff201 ∷ CCZ123 ∷ K2 ∷ CS12 ∷ CX01 ∷ Sw01 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K2 ∷ ι1 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ [])
  b0 = at 1 0 (Toff201 ∷ Toff201 ∷ []) wn01521 ▸
       at 5 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 4 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (Sw01 ∷ ι1 ∷ []) wn00127 ▸
       at 10 2 (Sw01 ∷ K2 ∷ []) (sym (low-comm (Swap) (K))) ▸
       at 9 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 8 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 7 2 (Sw01 ∷ CS02⁻ ∷ []) wn00009 ▸ done

  b1 : Chain (CZ12 ∷ Toff201 ∷ Toff201 ∷ CCZ123 ∷ K2 ∷ CS12 ∷ CX01 ∷ Sw01 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K2 ∷ ι1 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (CZ12 ∷ Toff201 ∷ Toff201 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ CS12 ∷ Sw01 ∷ Sw23 ∷ Toff201 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ [])
  b1 = at 6 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 5 2 (Sw01 ∷ CS02 ∷ []) wn00010 ▸
       at 4 2 (Sw01 ∷ K2 ∷ []) (sym (low-comm (Swap) (K))) ▸
       at 5 8 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) wn00333 ▸
       at 5 8 (Toff201 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b2 : Chain (CZ12 ∷ Toff201 ∷ Toff201 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ CS12 ∷ Sw01 ∷ Sw23 ∷ Toff201 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (CZ12 ∷ Toff201 ∷ Toff201 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Toff201 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ [])
  b2 = at 8 2 (Sw01 ∷ CS02 ∷ []) wn00010 ▸
       at 7 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw01 ∷ CX02 ∷ []) wn00253 ▸
       at 5 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 4 2 (Sw01 ∷ CX02 ∷ []) wn00253 ▸
       at 3 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 4 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸ done

  b3 : Chain (CZ12 ∷ Toff201 ∷ Toff201 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Toff201 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (CZ12 ∷ Toff201 ∷ Toff201 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Toff201 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ [])
  b3 = at 5 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 6 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 7 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 8 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b4 : Chain (CZ12 ∷ Toff201 ∷ Toff201 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Toff201 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (CZ12 ∷ Toff201 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw01 ∷ CS12 ∷ K2 ∷ ι1 ∷ CCZ023 ∷ Toff201 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ [])
  b4 = at 9 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸
       at 5 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 4 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw01 ∷ ι1 ∷ []) wn00127 ▸
       at 8 2 (Sw01 ∷ K2 ∷ []) (sym (low-comm (Swap) (K))) ▸
       at 7 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸ done

  b5 : Chain (CZ12 ∷ Toff201 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw01 ∷ CS12 ∷ K2 ∷ ι1 ∷ CCZ023 ∷ Toff201 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (CZ12 ∷ Toff201 ∷ Sw01 ∷ Toff201 ∷ CCZ023 ∷ Toff201 ∷ Sw12 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ [])
  b5 = at 6 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 5 2 (Sw01 ∷ CS02⁻ ∷ []) wn00009 ▸
       at 4 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 3 2 (Sw01 ∷ CS02 ∷ []) wn00010 ▸
       at 2 2 (Sw01 ∷ K2 ∷ []) (sym (low-comm (Swap) (K))) ▸
       at 3 8 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) wn00333 ▸
       at 3 8 (Toff201 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸ done

  b6 : Chain (CZ12 ∷ Toff201 ∷ Sw01 ∷ Toff201 ∷ CCZ023 ∷ Toff201 ∷ Sw12 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (CZ12 ∷ Toff201 ∷ Sw01 ∷ Toff201 ∷ CCZ023 ∷ K2 ∷ CS12 ∷ CX01 ∷ Sw12 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ [])
  b6 = at 5 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (Sw12 ∷ ι ∷ []) (low₁-comm (iI) (Swap)) ▸
       at 11 2 (Sw12 ∷ K1 ∷ []) wn00398 ▸
       at 10 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] wn00014 ▸
       at 9 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 10 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw12 ∷ CS12⁻ ∷ []) wn00015 ▸ done

  b7 : Chain (CZ12 ∷ Toff201 ∷ Sw01 ∷ Toff201 ∷ CCZ023 ∷ K2 ∷ CS12 ∷ CX01 ∷ Sw12 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (CZ12 ∷ Toff201 ∷ Sw01 ∷ Toff201 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw12 ∷ Toff102 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ [])
  b7 = at 7 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 8 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw12 ∷ CS12 ∷ []) wn00016 ▸
       at 5 2 (Sw12 ∷ K1 ∷ []) wn00398 ▸
       at 6 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) wn00366 ▸
       at 6 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b8 : Chain (CZ12 ∷ Toff201 ∷ Sw01 ∷ Toff201 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw12 ∷ Toff102 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (CZ12 ∷ Toff201 ∷ Sw01 ∷ Toff201 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Toff102 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ [])
  b8 = at 4 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 5 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 6 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 7 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b9 : Chain (CZ12 ∷ Toff201 ∷ Sw01 ∷ Toff201 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Toff102 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (CZ12 ∷ Toff201 ∷ Sw01 ∷ Toff201 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS03 ∷ Toff102 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ [])
  b9 = at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00031 ▸
       at 8 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) wn00022 ▸
       at 10 2 (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap)) ▸
       at 8 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) wn00023 ▸
       at 9 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸ done

  b10 : Chain (CZ12 ∷ Toff201 ∷ Sw01 ∷ Toff201 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS03 ∷ Toff102 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (CZ12 ∷ Toff201 ∷ Sw01 ∷ Toff201 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Toff102 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ [])
  b10 = at 9 2 [] wn00014 ▸
       at 6 2 (Sw12 ∷ CS13⁻ ∷ []) wn00047 ▸
       at 5 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00014 ▸
       at 4 2 (Sw12 ∷ CS13 ∷ []) wn00048 ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸ done

  b11 : Chain (CZ12 ∷ Toff201 ∷ Sw01 ∷ Toff201 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Toff102 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (CZ12 ∷ Toff201 ∷ Sw01 ∷ Toff201 ∷ Sw12 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Toff102 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ [])
  b11 = at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00003 ▸
       at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00003 ▸
       at 6 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00043 ▸
       at 6 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸ done

  b12 : Chain (CZ12 ∷ Toff201 ∷ Sw01 ∷ Toff201 ∷ Sw12 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Toff102 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (CZ12 ∷ Toff201 ∷ Sw01 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw12 ∷ CX02 ∷ CS01 ∷ K1 ∷ ι ∷ CCZ013 ∷ Toff102 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ [])
  b12 = at 5 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw12 ∷ ι ∷ []) (low₁-comm (iI) (Swap)) ▸
       at 9 2 (Sw12 ∷ K1 ∷ []) wn00398 ▸
       at 8 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00014 ▸
       at 7 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 8 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸ done

  b13 : Chain (CZ12 ∷ Toff201 ∷ Sw01 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw12 ∷ CX02 ∷ CS01 ∷ K1 ∷ ι ∷ CCZ013 ∷ Toff102 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Toff102 ∷ CCZ013 ∷ Toff102 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ [])
  b13 = at 6 2 (Sw12 ∷ CS12⁻ ∷ []) wn00015 ▸
       at 5 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 6 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw12 ∷ CS12 ∷ []) wn00016 ▸
       at 3 2 (Sw12 ∷ K1 ∷ []) wn00398 ▸
       at 4 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) wn00366 ▸
       at 4 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸ done

  b14 : Chain (CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Toff102 ∷ CCZ013 ∷ Toff102 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Toff102 ∷ CCZ013 ∷ K1 ∷ Sw01 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K0 ∷ ι1 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ [])
  b14 = at 6 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (Sw01 ∷ ι1 ∷ []) wn00127 ▸
       at 12 2 (Sw01 ∷ K0 ∷ []) wn00271 ▸
       at 11 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 10 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 9 2 (Sw01 ∷ CS02⁻ ∷ []) wn00009 ▸
       at 8 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 7 2 (Sw01 ∷ CS02 ∷ []) wn00010 ▸ done

  b15 : Chain (CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Toff102 ∷ CCZ013 ∷ K1 ∷ Sw01 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K0 ∷ ι1 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Toff102 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ [])
  b15 = at 6 2 (Sw01 ∷ K0 ∷ []) wn00271 ▸
       at 7 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) wn00272 ▸
       at 7 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b16 : Chain (CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Toff102 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Toff102 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ [])
  b16 = at 9 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 7 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00003 ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b17 : Chain (CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Toff102 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Toff102 ∷ CS13 ∷ CX01 ∷ Sw01 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ CX10 ∷ CS13 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ [])
  b17 = at 10 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 9 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 10 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 8 2 (Sw01 ∷ CS02⁻ ∷ []) wn00009 ▸
       at 7 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b18 : Chain (CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Toff102 ∷ CS13 ∷ CX01 ∷ Sw01 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ CX10 ∷ CS13 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Toff102 ∷ Sw01 ∷ Sw23 ∷ Sw23 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ [])
  b18 = at 8 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 6 2 (Sw01 ∷ CS02 ∷ []) wn00010 ▸
       at 5 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b19 : Chain (CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Toff102 ∷ Sw01 ∷ Sw23 ∷ Sw23 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Toff102 ∷ Sw01 ∷ Sw23 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Sw23 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ [])
  b19 = at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00003 ▸
       at 8 2 (CX10 ∷ Sw23 ∷ []) (sym (low-comm (CX₁₀) (Swap))) ▸
       at 10 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00003 ▸
       at 10 2 (CX10 ∷ Sw23 ∷ []) (sym (low-comm (CX₁₀) (Swap))) ▸
       at 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] wn00003 ▸ done

  b20 : Chain (CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Toff102 ∷ Sw01 ∷ Sw23 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Sw23 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw01 ∷ CX10 ∷ CS12 ∷ K0 ∷ ι1 ∷ CCZ013 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ [])
  b20 = at 7 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00011 ▸
       at 7 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 6 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (Sw01 ∷ ι1 ∷ []) wn00127 ▸
       at 10 2 (Sw01 ∷ K0 ∷ []) wn00271 ▸
       at 9 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 8 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸ done

  b21 : Chain (CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw01 ∷ CX10 ∷ CS12 ∷ K0 ∷ ι1 ∷ CCZ013 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ [])
  b21 = at 7 2 (Sw01 ∷ CS02⁻ ∷ []) wn00009 ▸
       at 6 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 5 2 (Sw01 ∷ CS02 ∷ []) wn00010 ▸
       at 4 2 (Sw01 ∷ K0 ∷ []) wn00271 ▸
       at 5 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) wn00272 ▸
       at 5 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (CCZ013 ∷ CCZ123 ∷ []) (ax toff-ccz) ▸
       at 5 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b22 : Chain (CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ [])
  b22 = at 6 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 7 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b23 : Chain (CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ CS03 ∷ CX10 ∷ Sw01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ [])
  b23 = at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00003 ▸
       at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 4 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX10 ∷ Sw01 ∷ []) wn00028 ▸ done

  b24 : Chain (CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ CS03 ∷ CX10 ∷ Sw01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ Sw23 ∷ Sw01 ∷ CS02 ∷ Sw23 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ [])
  b24 = at 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX10 ∷ Sw01 ∷ []) wn00028 ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b25 : Chain (CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ Sw23 ∷ Sw01 ∷ CS02 ∷ Sw23 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ CS02 ∷ CX10 ∷ Sw23 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ CX10 ∷ CS13 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ [])
  b25 = at 9 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 6 2 (CX10 ∷ Sw23 ∷ []) (sym (low-comm (CX₁₀) (Swap))) ▸
       at 8 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b26 : Chain (CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ CS02 ∷ CX10 ∷ Sw23 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ CX10 ∷ CS13 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ CCZ013 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ [])
  b26 = at 7 2 [] wn00003 ▸
       at 8 2 (CX10 ∷ Sw23 ∷ []) (sym (low-comm (CX₁₀) (Swap))) ▸
       at 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00003 ▸
       at 5 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00011 ▸
       at 5 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 4 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b27 : Chain (CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ CCZ013 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ CCZ013 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ [])
  b27 = at 5 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 6 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 7 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 8 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b28 : Chain (CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ CCZ013 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ CCZ013 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ Sw01 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ [])
  b28 = at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 6 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 7 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 8 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 9 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b29 : Chain (CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ CCZ013 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ Sw01 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ CCZ023 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ [])
  b29 = at 11 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 12 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸
       at 6 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00031 ▸
       at 4 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b30 : Chain (CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ CCZ023 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CCZ023 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ [])
  b30 = at 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b31 : Chain (CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CCZ023 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (CZ12 ∷ Toff201 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw12 ∷ CS03 ∷ CCZ023 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ [])
  b31 = at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00003 ▸
       at 3 2 (CS23 ∷ Sw12 ∷ []) wn00020 ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS23⁻ ∷ Sw12 ∷ []) wn00021 ▸
       at 8 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 6 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸ done

  b32 : Chain (CZ12 ∷ Toff201 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw12 ∷ CS03 ∷ CCZ023 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ Sw01 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw12 ∷ CCZ023 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ [])
  b32 = at 8 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) wn00022 ▸
       at 9 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 10 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) wn00023 ▸
       at 7 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 4 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 5 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸ done

  b33 : Chain (CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ Sw01 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw12 ∷ CCZ023 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw12 ∷ CCZ023 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ [])
  b33 = at 6 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 7 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸ done

  b34 : Chain (CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw12 ∷ CCZ023 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (CZ12 ∷ Toff201 ∷ Sw01 ∷ CCZ023 ∷ Sw12 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ [])
  b34 = at 4 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 6 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 7 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 8 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸ done

  b35 : Chain (CZ12 ∷ Toff201 ∷ Sw01 ∷ CCZ023 ∷ Sw12 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (CZ12 ∷ Toff201 ∷ Sw01 ∷ CCZ023 ∷ CS13 ∷ Sw12 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ [])
  b35 = at 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00031 ▸
       at 4 2 (CS13 ∷ Sw12 ∷ []) wn00049 ▸
       at 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸ done

  b36 : Chain (CZ12 ∷ Toff201 ∷ Sw01 ∷ CCZ023 ∷ CS13 ∷ Sw12 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (CZ12 ∷ Toff201 ∷ Sw01 ∷ CCZ023 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ [])
  b36 = at 5 2 [] wn00014 ▸
       at 6 2 (CS13⁻ ∷ Sw12 ∷ []) wn00051 ▸
       at 8 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00014 ▸
       at 9 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) wn00022 ▸
       at 10 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 11 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) wn00023 ▸ done

  b37 : Chain (CZ12 ∷ Toff201 ∷ Sw01 ∷ CCZ023 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (CZ12 ∷ Toff201 ∷ Sw01 ∷ CCZ023 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ CS03 ∷ Sw12 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ [])
  b37 = at 8 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00003 ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b38 : Chain (CZ12 ∷ Toff201 ∷ Sw01 ∷ CCZ023 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ CS03 ∷ Sw12 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ CCZ013 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ [])
  b38 = at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00003 ▸
       at 5 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00043 ▸
       at 5 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 4 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00014 ▸
       at 3 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b39 : Chain (CZ12 ∷ Toff201 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ CCZ013 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (CZ12 ∷ Toff201 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ CCZ013 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ [])
  b39 = at 3 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 4 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 5 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 6 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b40 : Chain (CZ12 ∷ Toff201 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ CCZ013 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (CZ12 ∷ Toff201 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ Sw01 ∷ CS02 ∷ Sw23 ∷ CCZ013 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ [])
  b40 = at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00031 ▸
       at 2 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 3 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 4 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 5 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b41 : Chain (CZ12 ∷ Toff201 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ Sw01 ∷ CS02 ∷ Sw23 ∷ CCZ013 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (CZ12 ∷ Toff201 ∷ CCZ123 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ [])
  b41 = at 7 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸
       at 2 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b42 : Chain (CZ12 ∷ Toff201 ∷ CCZ123 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (CZ12 ∷ Toff201 ∷ CCZ123 ∷ Sw01 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ [])
  b42 = at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00003 ▸ done

  b43 : Chain (CZ12 ∷ Toff201 ∷ CCZ123 ∷ Sw01 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (CZ12 ∷ Toff201 ∷ CCZ123 ∷ CS03 ∷ CX10 ∷ Sw23 ∷ Sw01 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ [])
  b43 = at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 4 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 3 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX10 ∷ Sw01 ∷ []) wn00028 ▸
       at 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b44 : Chain (CZ12 ∷ Toff201 ∷ CCZ123 ∷ CS03 ∷ CX10 ∷ Sw23 ∷ Sw01 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (CZ12 ∷ Toff201 ∷ CCZ123 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ [])
  b44 = at 6 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX10 ∷ Sw01 ∷ []) wn00028 ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b45 : Chain (CZ12 ∷ Toff201 ∷ CCZ123 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (CZ12 ∷ Toff201 ∷ CCZ123 ∷ Sw23 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ Sw23 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ [])
  b45 = at 7 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸
       at 5 2 (CX10 ∷ Sw23 ∷ []) (sym (low-comm (CX₁₀) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸
       at 7 2 (CX10 ∷ Sw23 ∷ []) (sym (low-comm (CX₁₀) (Swap))) ▸ done

  b46 : Chain (CZ12 ∷ Toff201 ∷ CCZ123 ∷ Sw23 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ Sw23 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (Toff201 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ CCZ123 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ [])
  b46 = at 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00003 ▸
       at 4 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00011 ▸
       at 4 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00031 ▸
       at 0 2 (Toff201 ∷ CZ01 ∷ CZ12 ∷ []) wn01991 ▸
       at 3 2 (CCZ013 ∷ CCZ123 ∷ []) (sym lem-pass-CCZ013-vs-CCZ123) ▸ done

  b47 : Chain (Toff201 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ CCZ123 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Toff201 ∷ CCZ123 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ Sw01 ∷ ι1 ∷ Sw01 ∷ CS23⁻ ∷ [])
  b47 = at 4 2 (CS23 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-CS23) ▸
       at 3 2 (CS23 ∷ CCZ013 ∷ []) (lem-pass-CCZ013-vs-CS23) ▸
       at 2 2 (CS23 ∷ CZ12 ∷ []) (lem-pass-CZ12-vs-CS23) ▸
       at 1 2 (CS23 ∷ CZ01 ∷ []) (lem-pass-CZ01-vs-CS23) ▸
       at 5 0 (Toff201 ∷ Toff201 ∷ []) wn01521 ▸
       at 9 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 8 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 (Sw01 ∷ ι1 ∷ []) wn00127 ▸ done

  b48 : Chain (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Toff201 ∷ CCZ123 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ Sw01 ∷ ι1 ∷ Sw01 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Toff201 ∷ CCZ123 ∷ Sw01 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw01 ∷ CS23⁻ ∷ [])
  b48 = at 14 2 (Sw01 ∷ K2 ∷ []) (sym (low-comm (Swap) (K))) ▸
       at 13 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 12 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 11 2 (Sw01 ∷ CS02⁻ ∷ []) wn00009 ▸
       at 10 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 9 2 (Sw01 ∷ CS02 ∷ []) wn00010 ▸
       at 8 2 (Sw01 ∷ K2 ∷ []) (sym (low-comm (Swap) (K))) ▸
       at 9 8 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) wn00333 ▸ done

  b49 : Chain (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Toff201 ∷ CCZ123 ∷ Sw01 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw01 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Toff201 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ Sw01 ∷ CX02 ∷ CS03 ∷ Toff201 ∷ Sw01 ∷ CS23⁻ ∷ [])
  b49 = at 9 8 (Toff201 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 12 2 (Sw01 ∷ CS02 ∷ []) wn00010 ▸
       at 11 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 12 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw01 ∷ CX02 ∷ []) wn00253 ▸ done

  b50 : Chain (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Toff201 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ Sw01 ∷ CX02 ∷ CS03 ∷ Toff201 ∷ Sw01 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Toff201 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw01 ∷ CS03 ∷ Toff201 ∷ Sw01 ∷ CS23⁻ ∷ [])
  b50 = at 9 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 8 2 (Sw01 ∷ CX02 ∷ []) wn00253 ▸
       at 7 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 8 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 9 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 10 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 11 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 12 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸ done

  b51 : Chain (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Toff201 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw01 ∷ CS03 ∷ Toff201 ∷ Sw01 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Toff201 ∷ Sw01 ∷ CCZ023 ∷ Toff201 ∷ Sw01 ∷ CS23⁻ ∷ [])
  b51 = at 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 14 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 15 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 13 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 9 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸
       at 9 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 8 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸ done

  b52 : Chain (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Toff201 ∷ Sw01 ∷ CCZ023 ∷ Toff201 ∷ Sw01 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ K2 ∷ Sw01 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K2 ∷ ι1 ∷ CCZ023 ∷ Toff201 ∷ Sw01 ∷ CS23⁻ ∷ [])
  b52 = at 6 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (Sw01 ∷ ι1 ∷ []) wn00127 ▸
       at 12 2 (Sw01 ∷ K2 ∷ []) (sym (low-comm (Swap) (K))) ▸
       at 11 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 10 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 9 2 (Sw01 ∷ CS02⁻ ∷ []) wn00009 ▸
       at 8 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 7 2 (Sw01 ∷ CS02 ∷ []) wn00010 ▸ done

  b53 : Chain (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ K2 ∷ Sw01 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K2 ∷ ι1 ∷ CCZ023 ∷ Toff201 ∷ Sw01 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Toff201 ∷ CCZ023 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw12 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ [])
  b53 = at 6 2 (Sw01 ∷ K2 ∷ []) (sym (low-comm (Swap) (K))) ▸
       at 7 8 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) wn00333 ▸
       at 7 8 (Toff201 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 9 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 16 2 (Sw12 ∷ ι ∷ []) (low₁-comm (iI) (Swap)) ▸
       at 15 2 (Sw12 ∷ K1 ∷ []) wn00398 ▸
       at 14 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸ done

  b54 : Chain (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Toff201 ∷ CCZ023 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw12 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Toff201 ∷ CCZ023 ∷ Sw12 ∷ K1 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ [])
  b54 = at 16 2 [] wn00014 ▸
       at 13 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 14 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (Sw12 ∷ CS12⁻ ∷ []) wn00015 ▸
       at 11 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 12 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw12 ∷ CS12 ∷ []) wn00016 ▸
       at 9 2 (Sw12 ∷ K1 ∷ []) wn00398 ▸ done

  b55 : Chain (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Toff201 ∷ CCZ023 ∷ Sw12 ∷ K1 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Toff201 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ Sw01 ∷ Sw12 ∷ Toff102 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ [])
  b55 = at 10 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) wn00366 ▸
       at 10 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 8 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 9 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 9 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 10 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 11 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸ done

  b56 : Chain (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Toff201 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ Sw01 ∷ Sw12 ∷ Toff102 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Toff201 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ Toff102 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ [])
  b56 = at 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 13 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 14 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 12 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 [] wn00031 ▸
       at 12 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 15 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) wn00022 ▸ done

  b57 : Chain (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Toff201 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ Toff102 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Toff201 ∷ CS23 ∷ Sw12 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Toff102 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ [])
  b57 = at 14 2 (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap)) ▸
       at 12 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) wn00023 ▸
       at 13 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 11 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 [] wn00014 ▸
       at 10 2 (Sw12 ∷ CS13⁻ ∷ []) wn00047 ▸
       at 9 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] wn00014 ▸ done

  b58 : Chain (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Toff201 ∷ CS23 ∷ Sw12 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Toff102 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Toff201 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ CS03 ∷ Toff102 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ [])
  b58 = at 8 2 (Sw12 ∷ CS13 ∷ []) wn00048 ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00003 ▸
       at 11 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 13 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] wn00003 ▸
       at 13 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b59 : Chain (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Toff201 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ CS03 ∷ Toff102 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw12 ∷ K1 ∷ ι ∷ CCZ013 ∷ Toff102 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ [])
  b59 = at 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 [] wn00003 ▸
       at 10 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00043 ▸
       at 10 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 9 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 (Sw12 ∷ ι ∷ []) (low₁-comm (iI) (Swap)) ▸
       at 13 2 (Sw12 ∷ K1 ∷ []) wn00398 ▸ done

  b60 : Chain (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw12 ∷ K1 ∷ ι ∷ CCZ013 ∷ Toff102 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ K2 ∷ Sw12 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K1 ∷ ι ∷ CCZ013 ∷ Toff102 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ [])
  b60 = at 12 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 [] wn00014 ▸
       at 11 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 12 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw12 ∷ CS12⁻ ∷ []) wn00015 ▸
       at 9 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 10 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw12 ∷ CS12 ∷ []) wn00016 ▸ done

  b61 : Chain (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ K2 ∷ Sw12 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K1 ∷ ι ∷ CCZ013 ∷ Toff102 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Toff102 ∷ CCZ013 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw01 ∷ CS12 ∷ K0 ∷ ι1 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ [])
  b61 = at 7 2 (Sw12 ∷ K1 ∷ []) wn00398 ▸
       at 8 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) wn00366 ▸
       at 8 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 11 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 10 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 17 2 (Sw01 ∷ ι1 ∷ []) wn00127 ▸
       at 16 2 (Sw01 ∷ K0 ∷ []) wn00271 ▸
       at 15 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸ done

  b62 : Chain (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Toff102 ∷ CCZ013 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw01 ∷ CS12 ∷ K0 ∷ ι1 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Toff102 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw01 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ [])
  b62 = at 14 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 13 2 (Sw01 ∷ CS02⁻ ∷ []) wn00009 ▸
       at 12 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 11 2 (Sw01 ∷ CS02 ∷ []) wn00010 ▸
       at 10 2 (Sw01 ∷ K0 ∷ []) wn00271 ▸
       at 11 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) wn00272 ▸
       at 11 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 9 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b63 : Chain (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Toff102 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw01 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Toff102 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ Sw01 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ [])
  b63 = at 10 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 9 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 13 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 11 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 15 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b64 : Chain (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Toff102 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ Sw01 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Toff102 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw01 ∷ CX10 ∷ CS13 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ [])
  b64 = at 13 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 [] wn00003 ▸
       at 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 14 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 13 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 14 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸ done

  b65 : Chain (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Toff102 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw01 ∷ CX10 ∷ CS13 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Toff102 ∷ Sw23 ∷ CS12 ∷ Sw01 ∷ Sw23 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ [])
  b65 = at 11 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 12 2 (Sw01 ∷ CS02⁻ ∷ []) wn00009 ▸
       at 11 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 12 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b66 : Chain (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Toff102 ∷ Sw23 ∷ CS12 ∷ Sw01 ∷ Sw23 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Toff102 ∷ Sw01 ∷ Sw23 ∷ CS02 ∷ CX10 ∷ Sw23 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ CX10 ∷ CS13 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ [])
  b66 = at 10 2 (Sw01 ∷ CS02 ∷ []) wn00010 ▸
       at 9 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 10 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] wn00003 ▸
       at 12 2 (CX10 ∷ Sw23 ∷ []) (sym (low-comm (CX₁₀) (Swap))) ▸
       at 14 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b67 : Chain (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Toff102 ∷ Sw01 ∷ Sw23 ∷ CS02 ∷ CX10 ∷ Sw23 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ CX10 ∷ CS13 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw01 ∷ CCZ013 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ [])
  b67 = at 13 2 [] wn00003 ▸
       at 14 2 (CX10 ∷ Sw23 ∷ []) (sym (low-comm (CX₁₀) (Swap))) ▸
       at 16 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 [] wn00003 ▸
       at 11 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00011 ▸
       at 11 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 10 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 8 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸ done

  b68 : Chain (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw01 ∷ CCZ013 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ K0 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K0 ∷ ι1 ∷ CCZ013 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ [])
  b68 = at 15 2 (Sw01 ∷ ι1 ∷ []) wn00127 ▸
       at 14 2 (Sw01 ∷ K0 ∷ []) wn00271 ▸
       at 13 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 12 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 11 2 (Sw01 ∷ CS02⁻ ∷ []) wn00009 ▸
       at 10 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 9 2 (Sw01 ∷ CS02 ∷ []) wn00010 ▸
       at 8 2 (Sw01 ∷ K0 ∷ []) wn00271 ▸ done

  b69 : Chain (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ K0 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K0 ∷ ι1 ∷ CCZ013 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ [])
  b69 = at 9 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) wn00272 ▸
       at 9 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 9 3 (CCZ013 ∷ CCZ123 ∷ []) (ax toff-ccz) ▸
       at 9 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 9 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b70 : Chain (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ [])
  b70 = at 13 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 11 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 15 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 13 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 [] wn00003 ▸
       at 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b71 : Chain (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ CS03 ∷ CX10 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Sw01 ∷ CX01 ∷ CS03 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ [])
  b71 = at 9 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CX10 ∷ Sw01 ∷ []) wn00028 ▸
       at 11 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 11 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸
       at 12 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b72 : Chain (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ CS03 ∷ CX10 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Sw01 ∷ CX01 ∷ CS03 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ [])
  b72 = at 10 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (CX10 ∷ Sw01 ∷ []) wn00028 ▸
       at 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 13 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 14 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 12 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b73 : Chain (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ [])
  b73 = at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00003 ▸
       at 10 2 (CX10 ∷ Sw23 ∷ []) (sym (low-comm (CX₁₀) (Swap))) ▸
       at 12 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] wn00003 ▸
       at 12 2 (CX10 ∷ Sw23 ∷ []) (sym (low-comm (CX₁₀) (Swap))) ▸
       at 14 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 [] wn00003 ▸ done

  b74 : Chain (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ CCZ013 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ [])
  b74 = at 9 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00011 ▸
       at 9 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 8 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 10 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 10 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 11 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 12 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸ done

  b75 : Chain (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ CCZ013 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ CCZ013 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ Sw01 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ [])
  b75 = at 14 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 14 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 15 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 13 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 10 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 11 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸ done

  b76 : Chain (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ CCZ013 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ Sw01 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ CCZ013 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ [])
  b76 = at 12 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 13 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 15 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 16 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 14 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 10 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸ done

  b77 : Chain (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ CCZ013 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ CCZ023 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ [])
  b77 = at 10 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 9 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00031 ▸
       at 8 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 8 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b78 : Chain (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw12 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ CCZ023 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ CS23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ CCZ023 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ [])
  b78 = at 12 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 10 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 14 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 12 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 [] wn00003 ▸
       at 7 2 (CS23 ∷ Sw12 ∷ []) wn00020 ▸
       at 10 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸ done

  b79 : Chain (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ CS23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ CCZ023 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ CCZ023 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ [])
  b79 = at 8 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CS23⁻ ∷ Sw12 ∷ []) wn00021 ▸
       at 12 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 10 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 12 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) wn00022 ▸
       at 13 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 14 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) wn00023 ▸ done

  b80 : Chain (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ CCZ023 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ Sw01 ∷ CS02 ∷ Sw23 ∷ Sw12 ∷ CCZ023 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ [])
  b80 = at 11 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 8 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 9 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 10 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 11 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b81 : Chain (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ Sw01 ∷ CS02 ∷ Sw23 ∷ Sw12 ∷ CCZ023 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ CCZ023 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ [])
  b81 = at 13 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 14 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 12 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 8 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸
       at 8 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 7 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸
       at 9 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 10 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b82 : Chain (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ CCZ023 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ CCZ023 ∷ Sw12 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ [])
  b82 = at 9 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 10 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 11 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 12 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 14 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 14 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 15 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b83 : Chain (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ CCZ023 ∷ Sw12 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ CCZ023 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw12 ∷ CS03 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ [])
  b83 = at 13 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 [] wn00031 ▸
       at 8 2 (CS13 ∷ Sw12 ∷ []) wn00049 ▸
       at 10 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00014 ▸
       at 10 2 (CS13⁻ ∷ Sw12 ∷ []) wn00051 ▸
       at 12 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] wn00014 ▸ done

  b84 : Chain (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ CCZ023 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw12 ∷ CS03 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ CCZ023 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw12 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ [])
  b84 = at 13 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) wn00022 ▸
       at 14 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 15 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) wn00023 ▸
       at 12 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00003 ▸ done

  b85 : Chain (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ CCZ023 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw12 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ CCZ023 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ [])
  b85 = at 10 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 12 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] wn00003 ▸
       at 12 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 [] wn00003 ▸
       at 9 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00043 ▸
       at 9 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸ done

  b86 : Chain (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ CCZ023 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw01 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ Sw01 ∷ CCZ013 ∷ Sw01 ∷ CS23⁻ ∷ [])
  b86 = at 8 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00014 ▸
       at 7 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 8 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 8 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 9 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 10 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸ done

  b87 : Chain (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ Sw01 ∷ CCZ013 ∷ Sw01 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ CS23 ∷ CX12 ∷ Sw01 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ CCZ013 ∷ Sw01 ∷ CS23⁻ ∷ [])
  b87 = at 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 12 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 13 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 11 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] wn00031 ▸
       at 6 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 7 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸ done

  b88 : Chain (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ CS23 ∷ CX12 ∷ Sw01 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ CCZ013 ∷ Sw01 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ CCZ013 ∷ Sw01 ∷ CS23⁻ ∷ [])
  b88 = at 8 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 9 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 11 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 12 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸ done

  b89 : Chain (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ CCZ013 ∷ Sw01 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ CCZ123 ∷ Sw01 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ CS23⁻ ∷ [])
  b89 = at 6 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 8 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 8 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 10 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b90 : Chain (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ CCZ123 ∷ Sw01 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ CCZ123 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw01 ∷ CS23⁻ ∷ [])
  b90 = at 11 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 14 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 12 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 [] wn00003 ▸
       at 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b91 : Chain (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ CCZ123 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw01 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ CCZ123 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ Sw01 ∷ CS03 ∷ Sw01 ∷ CS23⁻ ∷ [])
  b91 = at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX10 ∷ Sw01 ∷ []) wn00028 ▸
       at 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (CX10 ∷ Sw01 ∷ []) wn00028 ▸ done

  b92 : Chain (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ CCZ123 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ Sw01 ∷ CS03 ∷ Sw01 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ CCZ123 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ CS23⁻ ∷ [])
  b92 = at 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 12 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 13 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 11 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00003 ▸ done

  b93 : Chain (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ CCZ123 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ CCZ123 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ CS23⁻ ∷ [])
  b93 = at 9 2 (CX10 ∷ Sw23 ∷ []) (sym (low-comm (CX₁₀) (Swap))) ▸
       at 11 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00003 ▸
       at 11 2 (CX10 ∷ Sw23 ∷ []) (sym (low-comm (CX₁₀) (Swap))) ▸
       at 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] wn00003 ▸
       at 8 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00011 ▸
       at 8 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸ done

  b94 : Chain (Toff201 ∷ CS23 ∷ CZ01 ∷ CZ12 ∷ CCZ013 ∷ Toff201 ∷ CCZ123 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ Toff201 ∷ CZ12 ∷ CCZ013 ∷ CCZ013 ∷ Sw23 ∷ Sw23 ∷ CCZ123 ∷ CS23⁻ ∷ [])
  b94 = at 7 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00031 ▸
       at 4 2 (Toff201 ∷ CCZ013 ∷ []) (lem-pass-CCZ013-vs-TOFF201) ▸
       at 3 2 (Toff201 ∷ CZ01 ∷ CZ12 ∷ []) wn01991 ▸
       at 2 2 (Toff201 ∷ CZ01 ∷ []) wn01992 ▸
       at 7 2 (CCZ013 ∷ CCZ123 ∷ []) (sym lem-pass-CCZ013-vs-CCZ123) ▸
       at 3 2 [] wn01877 ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b95 : Chain (Toff201 ∷ CS23 ∷ Toff201 ∷ CZ12 ∷ CCZ013 ∷ CCZ013 ∷ Sw23 ∷ Sw23 ∷ CCZ123 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ Toff201 ∷ CZ12 ∷ CCZ013 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CCZ123 ∷ CS23⁻ ∷ [])
  b95 = at 5 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 7 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b96 : Chain (Toff201 ∷ CS23 ∷ Toff201 ∷ CZ12 ∷ CCZ013 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CCZ123 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ Toff201 ∷ CZ12 ∷ CCZ013 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ CCZ123 ∷ CS23⁻ ∷ [])
  b96 = at 11 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00003 ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] wn00003 ▸
       at 8 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00003 ▸ done

  b97 : Chain (Toff201 ∷ CS23 ∷ Toff201 ∷ CZ12 ∷ CCZ013 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ CCZ123 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ Toff201 ∷ CZ12 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ CCZ123 ∷ CS23⁻ ∷ [])
  b97 = at 6 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00003 ▸
       at 6 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00043 ▸
       at 6 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b98 : Chain (Toff201 ∷ CS23 ∷ Toff201 ∷ CZ12 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ CCZ123 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ Toff201 ∷ CZ12 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ CCZ123 ∷ CS23⁻ ∷ [])
  b98 = at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00003 ▸ done

  b99 : Chain (Toff201 ∷ CS23 ∷ Toff201 ∷ CZ12 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ CCZ123 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ Toff201 ∷ CZ12 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ CCZ012 ∷ Sw23 ∷ CCZ123 ∷ CS23⁻ ∷ [])
  b99 = at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00003 ▸
       at 7 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00003 ▸
       at 5 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸ done

  b100 : Chain (Toff201 ∷ CS23 ∷ Toff201 ∷ CZ12 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ CCZ012 ∷ Sw23 ∷ CCZ123 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ CZ12 ∷ CCZ123 ∷ [])
  b100 = at 5 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00043 ▸
       at 5 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00032 ▸
       at 4 2 [] wn00003 ▸
       at 4 2 (CS23⁻ ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-CSd23) ▸
       at 3 2 (CS23⁻ ∷ CZ12 ∷ []) (lem-pass-CZ12-vs-CSd23) ▸ done

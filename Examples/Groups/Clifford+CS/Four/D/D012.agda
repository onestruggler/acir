{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D012 where

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
open import Examples.Groups.Clifford+CS.Four.Wins.W01 using (wn00001 ; wn00003 ; wn00005 ; wn00007 ; wn00010 ; wn00011 ; wn00012 ; wn00014 ; wn00017 ; wn00018 ; wn00019 ; wn00020 ; wn00021 ; wn00022 ; wn00023 ; wn00024 ; wn00025 ; wn00026 ; wn00027 ; wn00028 ; wn00029 ; wn00030 ; wn00031 ; wn00032 ; wn00033 ; wn00036 ; wn00043 ; wn00044 ; wn00047 ; wn00048 ; wn00049 ; wn00051 ; wn00070 ; wn00074 ; wn00076)
open import Examples.Groups.Clifford+CS.Four.Wins.W02 using (wn00233 ; wn00238 ; wn00239 ; wn00240 ; wn00241 ; wn00252 ; wn00253 ; wn00254 ; wn00255 ; wn00256 ; wn00257 ; wn00258 ; wn00259 ; wn00260)

-- comm CCZ012 CCZ123: 455 steps
lem-comm-CCZ012-CCZ123 : ⟪ (CCZ012 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CCZ012 ∷ []) ⟫ʷ
lem-comm-CCZ012-CCZ123 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (trans (run b38) (trans (run b39) (trans (run b40) (trans (run b41) (trans (run b42) (trans (run b43) (trans (run b44) (trans (run b45) (trans (run b46) (trans (run b47) (trans (run b48) (trans (run b49) (trans (run b50) (trans (run b51) (trans (run b52) (trans (run b53) (trans (run b54) (trans (run b55) (run b56))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (CCZ012 ∷ CCZ123 ∷ []) (CCZ012 ∷ CCZ123 ∷ CX03 ∷ CCZ123 ∷ CCZ123 ∷ CX03 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 0 (CX02 ∷ CX02 ∷ []) wn00252 ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸
       at 3 0 (CCZ123 ∷ CCZ123 ∷ []) wn00070 ▸ done

  b1 : Chain (CCZ012 ∷ CCZ123 ∷ CX03 ∷ CCZ123 ∷ CCZ123 ∷ CX03 ∷ []) (CCZ012 ∷ CCZ123 ∷ CX03 ∷ CCZ123 ∷ CX03 ∷ Sw01 ∷ Sw01 ∷ CX03 ∷ CCZ123 ∷ CX03 ∷ [])
  b1 = at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 0 (CX02 ∷ CX02 ∷ []) wn00252 ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸
       at 5 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸ done

  b2 : Chain (CCZ012 ∷ CCZ123 ∷ CX03 ∷ CCZ123 ∷ CX03 ∷ Sw01 ∷ Sw01 ∷ CX03 ∷ CCZ123 ∷ CX03 ∷ []) (CCZ012 ∷ CCZ123 ∷ CX03 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ CS12 ∷ Sw01 ∷ Sw23 ∷ CX13 ∷ Sw01 ∷ CX03 ∷ CCZ123 ∷ CX03 ∷ [])
  b2 = at 4 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 5 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸
       at 4 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 5 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b3 : Chain (CCZ012 ∷ CCZ123 ∷ CX03 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ CS12 ∷ Sw01 ∷ Sw23 ∷ CX13 ∷ Sw01 ∷ CX03 ∷ CCZ123 ∷ CX03 ∷ []) (CCZ012 ∷ CCZ123 ∷ CX03 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ CX13 ∷ Sw01 ∷ CX03 ∷ CCZ123 ∷ CX03 ∷ [])
  b3 = at 8 2 (Sw01 ∷ CS02 ∷ []) wn00010 ▸
       at 7 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw01 ∷ CX02 ∷ []) wn00253 ▸
       at 5 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 4 2 (Sw01 ∷ CX02 ∷ []) wn00253 ▸
       at 3 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 4 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸ done

  b4 : Chain (CCZ012 ∷ CCZ123 ∷ CX03 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ CX13 ∷ Sw01 ∷ CX03 ∷ CCZ123 ∷ CX03 ∷ []) (CCZ012 ∷ CCZ123 ∷ CX03 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ CX13 ∷ Sw01 ∷ CX03 ∷ CCZ123 ∷ CX03 ∷ [])
  b4 = at 5 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 6 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 7 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 8 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b5 : Chain (CCZ012 ∷ CCZ123 ∷ CX03 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ CX13 ∷ Sw01 ∷ CX03 ∷ CCZ123 ∷ CX03 ∷ []) (CCZ012 ∷ CCZ123 ∷ Sw01 ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ CCZ023 ∷ CX13 ∷ Sw01 ∷ CX03 ∷ CCZ123 ∷ CX03 ∷ [])
  b5 = at 9 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸
       at 5 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 4 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 3 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸
       at 2 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b6 : Chain (CCZ012 ∷ CCZ123 ∷ Sw01 ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ CCZ023 ∷ CX13 ∷ Sw01 ∷ CX03 ∷ CCZ123 ∷ CX03 ∷ []) (CCZ012 ∷ CCZ123 ∷ Sw01 ∷ CX13 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw12 ∷ CX23 ∷ Sw12 ∷ Sw01 ∷ CX03 ∷ CCZ123 ∷ CX03 ∷ [])
  b6 = at 3 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 5 2 (Sw12 ∷ CX23 ∷ []) wn00036 ▸
       at 4 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 5 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 6 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸ done

  b7 : Chain (CCZ012 ∷ CCZ123 ∷ Sw01 ∷ CX13 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw12 ∷ CX23 ∷ Sw12 ∷ Sw01 ∷ CX03 ∷ CCZ123 ∷ CX03 ∷ []) (CCZ012 ∷ CCZ123 ∷ Sw01 ∷ CX13 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ CX23 ∷ Sw12 ∷ Sw01 ∷ CX03 ∷ CCZ123 ∷ CX03 ∷ [])
  b7 = at 7 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00031 ▸
       at 8 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b8 : Chain (CCZ012 ∷ CCZ123 ∷ Sw01 ∷ CX13 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ CX23 ∷ Sw12 ∷ Sw01 ∷ CX03 ∷ CCZ123 ∷ CX03 ∷ []) (CCZ012 ∷ CCZ123 ∷ Sw01 ∷ CX13 ∷ CS23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ CX23 ∷ Sw12 ∷ Sw01 ∷ CX03 ∷ CCZ123 ∷ CX03 ∷ [])
  b8 = at 11 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) wn00022 ▸
       at 10 2 (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap)) ▸
       at 8 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) wn00023 ▸
       at 9 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00014 ▸
       at 6 2 (Sw12 ∷ CS13⁻ ∷ []) wn00047 ▸
       at 5 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸ done

  b9 : Chain (CCZ012 ∷ CCZ123 ∷ Sw01 ∷ CX13 ∷ CS23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ CX23 ∷ Sw12 ∷ Sw01 ∷ CX03 ∷ CCZ123 ∷ CX03 ∷ []) (CCZ012 ∷ CCZ123 ∷ Sw01 ∷ CX13 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ CX23 ∷ Sw12 ∷ Sw01 ∷ CX03 ∷ CCZ123 ∷ CX03 ∷ [])
  b9 = at 7 2 [] wn00014 ▸
       at 4 2 (Sw12 ∷ CS13 ∷ []) wn00048 ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00003 ▸ done

  b10 : Chain (CCZ012 ∷ CCZ123 ∷ Sw01 ∷ CX13 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ CX23 ∷ Sw12 ∷ Sw01 ∷ CX03 ∷ CCZ123 ∷ CX03 ∷ []) (CCZ012 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ CX23 ∷ CCZ013 ∷ CX23 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ CX03 ∷ CCZ123 ∷ CX03 ∷ [])
  b10 = at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00003 ▸
       at 6 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00043 ▸
       at 6 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw12 ∷ CX23 ∷ []) wn00036 ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b11 : Chain (CCZ012 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ CX23 ∷ CCZ013 ∷ CX23 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ CX03 ∷ CCZ123 ∷ CX03 ∷ []) (CCZ012 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ CX23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CX32 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ CX03 ∷ CCZ123 ∷ CX03 ∷ [])
  b11 = at 6 2 (Sw23 ∷ CX32 ∷ []) wn00044 ▸
       at 5 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 7 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b12 : Chain (CCZ012 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ CX23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CX32 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ CX03 ∷ CCZ123 ∷ CX03 ∷ []) (CCZ012 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ CX23 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ CX32 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ CX03 ∷ CCZ123 ∷ CX03 ∷ [])
  b12 = at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00003 ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] wn00003 ▸
       at 8 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b13 : Chain (CCZ012 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ CX23 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ CX32 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ CX03 ∷ CCZ123 ∷ CX03 ∷ []) (CCZ012 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ CCZ012 ∷ CCZ013 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ CX03 ∷ CCZ123 ∷ CX03 ∷ [])
  b13 = at 9 2 [] wn00003 ▸
       at 6 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00003 ▸
       at 6 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00043 ▸
       at 6 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw23 ∷ CX32 ∷ []) wn00044 ▸
       at 5 3 (CCZ012 ∷ CCZ013 ∷ []) (ax cx-ccz) ▸ done

  b14 : Chain (CCZ012 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ CCZ012 ∷ CCZ013 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ CX03 ∷ CCZ123 ∷ CX03 ∷ []) (CCZ012 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CCZ013 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ CX03 ∷ CCZ123 ∷ CX03 ∷ [])
  b14 = at 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b15 : Chain (CCZ012 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CCZ013 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ CX03 ∷ CCZ123 ∷ CX03 ∷ []) (CCZ012 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ CS03 ∷ Sw23 ∷ CCZ013 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ CX03 ∷ CCZ123 ∷ CX03 ∷ [])
  b15 = at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00003 ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b16 : Chain (CCZ012 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ CS03 ∷ Sw23 ∷ CCZ013 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ CX03 ∷ CCZ123 ∷ CX03 ∷ []) (CCZ012 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ CCZ013 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ CX03 ∷ CCZ123 ∷ CX03 ∷ [])
  b16 = at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00003 ▸
       at 5 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00043 ▸
       at 5 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 4 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b17 : Chain (CCZ012 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ CCZ013 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ CX03 ∷ CCZ123 ∷ CX03 ∷ []) (CCZ012 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ CCZ013 ∷ Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ CX03 ∷ CCZ123 ∷ CX03 ∷ [])
  b17 = at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 8 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 10 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] wn00003 ▸ done

  b18 : Chain (CCZ012 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ CCZ013 ∷ Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ CX03 ∷ CCZ123 ∷ CX03 ∷ []) (CCZ012 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ CCZ013 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ CX03 ∷ CCZ123 ∷ CX03 ∷ [])
  b18 = at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00003 ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00003 ▸ done

  b19 : Chain (CCZ012 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ CCZ013 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ CX03 ∷ CCZ123 ∷ CX03 ∷ []) (CCZ012 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ CCZ012 ∷ Sw12 ∷ Sw01 ∷ CX03 ∷ CCZ123 ∷ CX03 ∷ [])
  b19 = at 5 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00043 ▸
       at 5 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸
       at 4 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b20 : Chain (CCZ012 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ CCZ012 ∷ Sw12 ∷ Sw01 ∷ CX03 ∷ CCZ123 ∷ CX03 ∷ []) (CCZ012 ∷ CCZ123 ∷ Sw01 ∷ CS23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ CCZ012 ∷ Sw12 ∷ Sw01 ∷ CX03 ∷ CCZ123 ∷ CX03 ∷ [])
  b20 = at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00003 ▸
       at 3 2 (CS23 ∷ Sw12 ∷ []) wn00020 ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸ done

  b21 : Chain (CCZ012 ∷ CCZ123 ∷ Sw01 ∷ CS23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ CCZ012 ∷ Sw12 ∷ Sw01 ∷ CX03 ∷ CCZ123 ∷ CX03 ∷ []) (CCZ012 ∷ CCZ123 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ CCZ012 ∷ Sw12 ∷ Sw01 ∷ CX03 ∷ CCZ123 ∷ CX03 ∷ [])
  b21 = at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS23⁻ ∷ Sw12 ∷ []) wn00021 ▸
       at 8 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 6 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 8 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) wn00022 ▸
       at 9 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 10 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) wn00023 ▸ done

  b22 : Chain (CCZ012 ∷ CCZ123 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ CCZ012 ∷ Sw12 ∷ Sw01 ∷ CX03 ∷ CCZ123 ∷ CX03 ∷ []) (CCZ012 ∷ CCZ123 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ Sw01 ∷ CS02 ∷ Sw23 ∷ Sw12 ∷ CCZ012 ∷ Sw12 ∷ Sw01 ∷ CX03 ∷ CCZ123 ∷ CX03 ∷ [])
  b22 = at 7 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 4 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 5 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 6 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 7 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b23 : Chain (CCZ012 ∷ CCZ123 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ Sw01 ∷ CS02 ∷ Sw23 ∷ Sw12 ∷ CCZ012 ∷ Sw12 ∷ Sw01 ∷ CX03 ∷ CCZ123 ∷ CX03 ∷ []) (CCZ012 ∷ CCZ123 ∷ Sw01 ∷ CCZ023 ∷ CS12 ∷ Sw12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw12 ∷ Sw01 ∷ CX03 ∷ CCZ123 ∷ CX03 ∷ [])
  b23 = at 9 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸
       at 4 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS12 ∷ Sw12 ∷ []) wn00018 ▸ done

  b24 : Chain (CCZ012 ∷ CCZ123 ∷ Sw01 ∷ CCZ023 ∷ CS12 ∷ Sw12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw12 ∷ Sw01 ∷ CX03 ∷ CCZ123 ∷ CX03 ∷ []) (CCZ012 ∷ CCZ123 ∷ Sw01 ∷ CCZ023 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw12 ∷ Sw12 ∷ Sw01 ∷ CX03 ∷ CCZ123 ∷ CX03 ∷ [])
  b24 = at 7 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 5 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS12⁻ ∷ Sw12 ∷ []) wn00019 ▸
       at 9 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 7 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 9 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00014 ▸
       at 4 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00017 ▸ done

  b25 : Chain (CCZ012 ∷ CCZ123 ∷ Sw01 ∷ CCZ023 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw12 ∷ Sw12 ∷ Sw01 ∷ CX03 ∷ CCZ123 ∷ CX03 ∷ []) (CCZ012 ∷ CCZ123 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ Sw01 ∷ CCZ012 ∷ Sw01 ∷ CX03 ∷ CCZ123 ∷ CX03 ∷ [])
  b25 = at 4 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00014 ▸
       at 3 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 4 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 5 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 6 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸ done

  b26 : Chain (CCZ012 ∷ CCZ123 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ Sw01 ∷ CCZ012 ∷ Sw01 ∷ CX03 ∷ CCZ123 ∷ CX03 ∷ []) (CCZ012 ∷ CCZ123 ∷ CS23 ∷ CX12 ∷ Sw01 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ CCZ012 ∷ Sw01 ∷ CX03 ∷ CCZ123 ∷ CX03 ∷ [])
  b26 = at 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00031 ▸
       at 2 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 3 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸ done

  b27 : Chain (CCZ012 ∷ CCZ123 ∷ CS23 ∷ CX12 ∷ Sw01 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ CCZ012 ∷ Sw01 ∷ CX03 ∷ CCZ123 ∷ CX03 ∷ []) (CCZ012 ∷ CCZ123 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ CCZ012 ∷ Sw01 ∷ CX03 ∷ CCZ123 ∷ CX03 ∷ [])
  b27 = at 4 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 5 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸ done

  b28 : Chain (CCZ012 ∷ CCZ123 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ CCZ012 ∷ Sw01 ∷ CX03 ∷ CCZ123 ∷ CX03 ∷ []) (CCZ012 ∷ CCZ123 ∷ CCZ123 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw01 ∷ Sw01 ∷ CX03 ∷ CCZ123 ∷ CX03 ∷ [])
  b28 = at 2 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 4 2 (CX10 ∷ Sw01 ∷ []) wn00028 ▸
       at 5 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸
       at 6 2 (CX10 ∷ Sw01 ∷ []) wn00028 ▸
       at 7 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 3 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00011 ▸ done

  b29 : Chain (CCZ012 ∷ CCZ123 ∷ CCZ123 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw01 ∷ Sw01 ∷ CX03 ∷ CCZ123 ∷ CX03 ∷ []) (CX03 ∷ CCZ123 ∷ Sw23 ∷ Sw01 ∷ CX12 ∷ Sw23 ∷ Sw01 ∷ [])
  b29 = at 3 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00031 ▸
       at 1 2 [] wn00033 ▸
       at 0 2 [] wn00032 ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 2 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 3 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸ done

  b30 : Chain (CX03 ∷ CCZ123 ∷ Sw23 ∷ Sw01 ∷ CX12 ∷ Sw23 ∷ Sw01 ∷ []) (CX03 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw01 ∷ CS03 ∷ CX13 ∷ Sw01 ∷ [])
  b30 = at 2 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 3 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 6 2 (Sw01 ∷ CS02 ∷ []) wn00010 ▸
       at 5 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b31 : Chain (CX03 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw01 ∷ CS03 ∷ CX13 ∷ Sw01 ∷ []) (CX03 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ Sw01 ∷ CX02 ∷ CS03 ∷ CX13 ∷ Sw01 ∷ [])
  b31 = at 4 2 (Sw01 ∷ CX02 ∷ []) wn00253 ▸
       at 3 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 2 2 (Sw01 ∷ CX02 ∷ []) wn00253 ▸
       at 1 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 3 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 4 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 5 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸ done

  b32 : Chain (CX03 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ Sw01 ∷ CX02 ∷ CS03 ∷ CX13 ∷ Sw01 ∷ []) (CX03 ∷ Sw01 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ CX13 ∷ Sw01 ∷ [])
  b32 = at 6 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸
       at 3 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸ done

  b33 : Chain (CX03 ∷ Sw01 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ CX13 ∷ Sw01 ∷ []) (Sw01 ∷ CX13 ∷ CCZ023 ∷ Sw12 ∷ CX23 ∷ Sw12 ∷ Sw01 ∷ [])
  b33 = at 2 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸
       at 0 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 1 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸
       at 0 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 1 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 3 2 (Sw12 ∷ CX23 ∷ []) wn00036 ▸ done

  b34 : Chain (Sw01 ∷ CX13 ∷ CCZ023 ∷ Sw12 ∷ CX23 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ CX13 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ CX23 ∷ Sw12 ∷ Sw01 ∷ [])
  b34 = at 2 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 3 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 4 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 5 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b35 : Chain (Sw01 ∷ CX13 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ CX23 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ CX13 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ CX23 ∷ Sw12 ∷ Sw01 ∷ [])
  b35 = at 7 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00031 ▸
       at 6 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) wn00022 ▸
       at 8 2 (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap)) ▸
       at 6 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) wn00023 ▸ done

  b36 : Chain (Sw01 ∷ CX13 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ CX23 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ CX13 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ CX23 ∷ Sw12 ∷ Sw01 ∷ [])
  b36 = at 7 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00014 ▸
       at 4 2 (Sw12 ∷ CS13⁻ ∷ []) wn00047 ▸
       at 3 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00014 ▸
       at 2 2 (Sw12 ∷ CS13 ∷ []) wn00048 ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b37 : Chain (Sw01 ∷ CX13 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ CX23 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ CX13 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ CX23 ∷ Sw12 ∷ Sw01 ∷ [])
  b37 = at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00003 ▸ done

  b38 : Chain (Sw01 ∷ CX13 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ CX23 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ CX23 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CX32 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ [])
  b38 = at 4 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00043 ▸
       at 4 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw12 ∷ CX23 ∷ []) wn00036 ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 2 (Sw23 ∷ CX32 ∷ []) wn00044 ▸
       at 3 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸ done

  b39 : Chain (Sw01 ∷ Sw12 ∷ CX23 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CX32 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ CX23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CX32 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ [])
  b39 = at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b40 : Chain (Sw01 ∷ Sw12 ∷ CX23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CX32 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ CX23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ CX32 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ [])
  b40 = at 8 2 [] wn00003 ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00003 ▸
       at 6 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00003 ▸
       at 4 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b41 : Chain (Sw01 ∷ Sw12 ∷ CX23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ CX32 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ CCZ013 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ [])
  b41 = at 5 2 [] wn00003 ▸
       at 4 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00043 ▸
       at 4 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw23 ∷ CX32 ∷ []) wn00044 ▸
       at 3 3 (CCZ012 ∷ CCZ013 ∷ []) (ax cx-ccz) ▸
       at 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b42 : Chain (Sw01 ∷ Sw12 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ CCZ013 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ CCZ013 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ [])
  b42 = at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b43 : Chain (Sw01 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ CCZ013 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CCZ013 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ [])
  b43 = at 3 2 [] wn00003 ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00003 ▸
       at 3 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00043 ▸ done

  b44 : Chain (Sw01 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CCZ013 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ CCZ013 ∷ Sw23 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ [])
  b44 = at 3 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b45 : Chain (Sw01 ∷ Sw12 ∷ CCZ013 ∷ Sw23 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ CCZ013 ∷ CS12 ∷ CX01 ∷ Sw23 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ [])
  b45 = at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00003 ▸
       at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b46 : Chain (Sw01 ∷ Sw12 ∷ CCZ013 ∷ CS12 ∷ CX01 ∷ Sw23 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ CCZ013 ∷ CCZ012 ∷ Sw12 ∷ Sw01 ∷ [])
  b46 = at 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00003 ▸
       at 3 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00043 ▸
       at 3 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸ done

  b47 : Chain (Sw01 ∷ Sw12 ∷ CCZ013 ∷ CCZ012 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ CCZ012 ∷ Sw12 ∷ Sw01 ∷ [])
  b47 = at 2 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b48 : Chain (Sw01 ∷ Sw12 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ CCZ012 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS03 ∷ CCZ012 ∷ Sw12 ∷ Sw01 ∷ [])
  b48 = at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00003 ▸
       at 1 2 (CS23 ∷ Sw12 ∷ []) wn00020 ▸
       at 4 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 2 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS23⁻ ∷ Sw12 ∷ []) wn00021 ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸ done

  b49 : Chain (Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS03 ∷ CCZ012 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw01 ∷ CS23 ∷ Sw01 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw12 ∷ CCZ012 ∷ Sw12 ∷ Sw01 ∷ [])
  b49 = at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) wn00022 ▸
       at 7 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 8 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) wn00023 ▸
       at 5 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 2 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸ done

  b50 : Chain (Sw01 ∷ Sw01 ∷ CS23 ∷ Sw01 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw12 ∷ CCZ012 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw12 ∷ CCZ012 ∷ Sw12 ∷ Sw01 ∷ [])
  b50 = at 3 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 4 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 5 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b51 : Chain (Sw01 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw12 ∷ CCZ012 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ023 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ Sw12 ∷ CX01 ∷ CS02 ∷ Sw12 ∷ Sw01 ∷ [])
  b51 = at 2 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸
       at 2 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CS12 ∷ Sw12 ∷ []) wn00018 ▸
       at 5 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 3 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS12⁻ ∷ Sw12 ∷ []) wn00019 ▸ done

  b52 : Chain (Sw01 ∷ CCZ023 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ Sw12 ∷ CX01 ∷ CS02 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ CCZ012 ∷ Sw01 ∷ [])
  b52 = at 7 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 5 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00014 ▸
       at 2 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00017 ▸
       at 2 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00014 ▸
       at 1 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸ done

  b53 : Chain (Sw01 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ CCZ012 ∷ Sw01 ∷ []) (Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ Sw01 ∷ CCZ012 ∷ Sw01 ∷ [])
  b53 = at 2 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 2 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 3 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 4 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸ done

  b54 : Chain (Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ Sw01 ∷ CCZ012 ∷ Sw01 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ CCZ012 ∷ Sw01 ∷ [])
  b54 = at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00031 ▸
       at 0 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 1 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 2 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 3 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b55 : Chain (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ CCZ012 ∷ Sw01 ∷ []) (CCZ123 ∷ CS02 ∷ Sw01 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw01 ∷ [])
  b55 = at 4 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 0 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸
       at 0 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸ done

  b56 : Chain (CCZ123 ∷ CS02 ∷ Sw01 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw01 ∷ []) (CCZ123 ∷ CCZ012 ∷ [])
  b56 = at 2 2 (CX10 ∷ Sw01 ∷ []) wn00028 ▸
       at 3 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸
       at 4 2 (CX10 ∷ Sw01 ∷ []) wn00028 ▸
       at 5 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 1 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00011 ▸
       at 1 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00031 ▸ done

-- pass [CCZ013] [CSd03]: 49 steps
lem-pass-CCZ013-vs-CSd03 : ⟪ (CCZ013 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ CCZ013 ∷ []) ⟫ʷ
lem-pass-CCZ013-vs-CSd03 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (run b6))))))
  where
  b0 : Chain (CCZ013 ∷ CS03⁻ ∷ []) (CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸
       at 0 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 0 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b1 : Chain (CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ CS02⁻ ∷ Sw23 ∷ [])
  b1 = at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸ done

  b2 : Chain (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ CS02⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CCZ012 ∷ CS02⁻ ∷ Sw23 ∷ [])
  b2 = at 3 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 2 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸
       at 1 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 0 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸
       at 1 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00043 ▸
       at 1 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (Sw23 ∷ CCZ012 ∷ CS02⁻ ∷ Sw23 ∷ []) (CS03⁻ ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ [])
  b3 = at 1 2 (CS02⁻ ∷ CCZ012 ∷ []) wn00254 ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 0 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b4 : Chain (CS03⁻ ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ []) (CS03⁻ ∷ Sw23 ∷ CS12 ∷ CX01 ∷ Sw23 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ [])
  b4 = at 3 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b5 : Chain (CS03⁻ ∷ Sw23 ∷ CS12 ∷ CX01 ∷ Sw23 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ []) (CS03⁻ ∷ CCZ013 ∷ Sw23 ∷ Sw23 ∷ [])
  b5 = at 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸
       at 2 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00043 ▸
       at 2 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸ done

  b6 : Chain (CS03⁻ ∷ CCZ013 ∷ Sw23 ∷ Sw23 ∷ []) (CS03⁻ ∷ CCZ013 ∷ [])
  b6 = at 2 2 [] wn00003 ▸ done

-- pass [X2 CS20 X2] [TOFF012]: 1 steps
lem-pass-X2-CS20-X2-vs-TOFF012 : ⟪ (X2 ∷ CS02 ∷ X2 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ X2 ∷ CS02 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CS20-X2-vs-TOFF012 = run b0
  where
  b0 : Chain (X2 ∷ CS02 ∷ X2 ∷ Toff012 ∷ []) (Toff012 ∷ X2 ∷ CS02 ∷ X2 ∷ [])
  b0 = at 0 4 (Toff012 ∷ X2 ∷ CS02 ∷ X2 ∷ []) wn00233 ▸ done

-- pass [X2 CS20 X2] [CS03]: 19 steps
lem-pass-X2-CS20-X2-vs-CS03 : ⟪ (X2 ∷ CS02 ∷ X2 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ X2 ∷ CS02 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CS20-X2-vs-CS03 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X2 ∷ CS02 ∷ X2 ∷ CS03 ∷ []) (X2 ∷ Sw01 ∷ CS12 ∷ X2 ∷ CS13 ∷ Sw01 ∷ [])
  b0 = at 4 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 4 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 3 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 1 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸ done

  b1 : Chain (X2 ∷ Sw01 ∷ CS12 ∷ X2 ∷ CS13 ∷ Sw01 ∷ []) (CS03 ∷ X2 ∷ Sw01 ∷ CS12 ∷ X2 ∷ Sw01 ∷ [])
  b1 = at 0 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 1 4 (CS13 ∷ X2 ∷ CS12 ∷ X2 ∷ []) wn00255 ▸
       at 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 0 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸ done

  b2 : Chain (CS03 ∷ X2 ∷ Sw01 ∷ CS12 ∷ X2 ∷ Sw01 ∷ []) (CS03 ∷ X2 ∷ CS02 ∷ X2 ∷ [])
  b2 = at 2 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 3 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 4 2 [] wn00031 ▸ done

-- pass [X2 CS20 X2] [CSd03]: 19 steps
lem-pass-X2-CS20-X2-vs-CSd03 : ⟪ (X2 ∷ CS02 ∷ X2 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ X2 ∷ CS02 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CS20-X2-vs-CSd03 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X2 ∷ CS02 ∷ X2 ∷ CS03⁻ ∷ []) (X2 ∷ Sw01 ∷ CS12 ∷ X2 ∷ CS13⁻ ∷ Sw01 ∷ [])
  b0 = at 4 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 3 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 4 2 (Sw01 ∷ CS12⁻ ∷ []) wn00076 ▸
       at 3 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 4 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 1 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸ done

  b1 : Chain (X2 ∷ Sw01 ∷ CS12 ∷ X2 ∷ CS13⁻ ∷ Sw01 ∷ []) (CS03⁻ ∷ X2 ∷ Sw01 ∷ CS12 ∷ X2 ∷ Sw01 ∷ [])
  b1 = at 0 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 1 4 (CS13⁻ ∷ X2 ∷ CS12 ∷ X2 ∷ []) wn00256 ▸
       at 1 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 0 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸ done

  b2 : Chain (CS03⁻ ∷ X2 ∷ Sw01 ∷ CS12 ∷ X2 ∷ Sw01 ∷ []) (CS03⁻ ∷ X2 ∷ CS02 ∷ X2 ∷ [])
  b2 = at 2 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 3 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 4 2 [] wn00031 ▸ done

-- pass [X2 CS20 X2] [TOFF102]: 1 steps
lem-pass-X2-CS20-X2-vs-TOFF102 : ⟪ (X2 ∷ CS02 ∷ X2 ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ X2 ∷ CS02 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CS20-X2-vs-TOFF102 = run b0
  where
  b0 : Chain (X2 ∷ CS02 ∷ X2 ∷ Toff102 ∷ []) (Toff102 ∷ X2 ∷ CS02 ∷ X2 ∷ [])
  b0 = at 0 4 (Toff102 ∷ X2 ∷ CS02 ∷ X2 ∷ []) wn00241 ▸ done

-- pass [X2 CS20 X2] [CS13]: 17 steps
lem-pass-X2-CS20-X2-vs-CS13 : ⟪ (X2 ∷ CS02 ∷ X2 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ X2 ∷ CS02 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CS20-X2-vs-CS13 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X2 ∷ CS02 ∷ X2 ∷ CS13 ∷ []) (X2 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ CS23 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ X2 ∷ [])
  b0 = at 2 2 (CS13 ∷ X2 ∷ []) wn00257 ▸
       at 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS23 ∷ Sw12 ∷ []) wn00020 ▸ done

  b1 : Chain (X2 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ CS23 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ X2 ∷ []) (X2 ∷ CS13 ∷ CS02 ∷ X2 ∷ [])
  b1 = at 4 2 (CS23 ∷ CS01 ∷ []) (low-comm (CS) (CS)) ▸
       at 3 2 (CS13 ∷ Sw12 ∷ []) wn00049 ▸
       at 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸
       at 3 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 1 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (X2 ∷ CS13 ∷ CS02 ∷ X2 ∷ []) (CS13 ∷ X2 ∷ CS02 ∷ X2 ∷ [])
  b2 = at 0 2 (CS13 ∷ X2 ∷ []) wn00257 ▸ done

-- pass [X2 CS20 X2] [CSd13]: 17 steps
lem-pass-X2-CS20-X2-vs-CSd13 : ⟪ (X2 ∷ CS02 ∷ X2 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ X2 ∷ CS02 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CS20-X2-vs-CSd13 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X2 ∷ CS02 ∷ X2 ∷ CS13⁻ ∷ []) (X2 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ CS23⁻ ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ X2 ∷ [])
  b0 = at 2 2 (CS13⁻ ∷ X2 ∷ []) wn00258 ▸
       at 2 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS23⁻ ∷ Sw12 ∷ []) wn00021 ▸ done

  b1 : Chain (X2 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ CS23⁻ ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ X2 ∷ []) (X2 ∷ CS13⁻ ∷ CS02 ∷ X2 ∷ [])
  b1 = at 4 2 (CS23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((CS • CS • CS))) ▸
       at 3 2 (CS13⁻ ∷ Sw12 ∷ []) wn00051 ▸
       at 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸
       at 3 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 1 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (X2 ∷ CS13⁻ ∷ CS02 ∷ X2 ∷ []) (CS13⁻ ∷ X2 ∷ CS02 ∷ X2 ∷ [])
  b2 = at 0 2 (CS13⁻ ∷ X2 ∷ []) wn00258 ▸ done

-- pass [X2 CK20 X2] [TOFF102]: 1 steps
lem-pass-X2-CK20-X2-vs-TOFF102 : ⟪ (X2 ∷ CK20 ∷ X2 ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ X2 ∷ CK20 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CK20-X2-vs-TOFF102 = run b0
  where
  b0 : Chain (X2 ∷ CK20 ∷ X2 ∷ Toff102 ∷ []) (Toff102 ∷ X2 ∷ CK20 ∷ X2 ∷ [])
  b0 = at 0 4 (Toff102 ∷ X2 ∷ CK20 ∷ X2 ∷ []) wn00240 ▸ done

-- pass [X2 CK20 X2] [CS13]: 17 steps
lem-pass-X2-CK20-X2-vs-CS13 : ⟪ (X2 ∷ CK20 ∷ X2 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ X2 ∷ CK20 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CK20-X2-vs-CS13 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X2 ∷ CK20 ∷ X2 ∷ CS13 ∷ []) (X2 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ CS23 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ X2 ∷ [])
  b0 = at 2 2 (CS13 ∷ X2 ∷ []) wn00257 ▸
       at 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CK30 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS23 ∷ Sw12 ∷ []) wn00020 ▸ done

  b1 : Chain (X2 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ CS23 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ X2 ∷ []) (X2 ∷ CS13 ∷ CK20 ∷ X2 ∷ [])
  b1 = at 4 2 (CS23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CS)) ▸
       at 3 2 (CS13 ∷ Sw12 ∷ []) wn00049 ▸
       at 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸
       at 3 5 (CK30 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 1 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (X2 ∷ CS13 ∷ CK20 ∷ X2 ∷ []) (CS13 ∷ X2 ∷ CK20 ∷ X2 ∷ [])
  b2 = at 0 2 (CS13 ∷ X2 ∷ []) wn00257 ▸ done

-- pass [X2 CK20 X2] [CSd13]: 17 steps
lem-pass-X2-CK20-X2-vs-CSd13 : ⟪ (X2 ∷ CK20 ∷ X2 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CK20-X2-vs-CSd13 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X2 ∷ CK20 ∷ X2 ∷ CS13⁻ ∷ []) (X2 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ CS23⁻ ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ X2 ∷ [])
  b0 = at 2 2 (CS13⁻ ∷ X2 ∷ []) wn00258 ▸
       at 2 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CK30 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS23⁻ ∷ Sw12 ∷ []) wn00021 ▸ done

  b1 : Chain (X2 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ CS23⁻ ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ X2 ∷ []) (X2 ∷ CS13⁻ ∷ CK20 ∷ X2 ∷ [])
  b1 = at 4 2 (CS23⁻ ∷ CK10 ∷ []) (low-comm (CK₁₀) ((CS • CS • CS))) ▸
       at 3 2 (CS13⁻ ∷ Sw12 ∷ []) wn00051 ▸
       at 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸
       at 3 5 (CK30 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 1 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (X2 ∷ CS13⁻ ∷ CK20 ∷ X2 ∷ []) (CS13⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ [])
  b2 = at 0 2 (CS13⁻ ∷ X2 ∷ []) wn00258 ▸ done

-- pass [X2 CKd20 X2] [TOFF102]: 1 steps
lem-pass-X2-CKd20-X2-vs-TOFF102 : ⟪ (X2 ∷ CK20⁻ ∷ X2 ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CKd20-X2-vs-TOFF102 = run b0
  where
  b0 : Chain (X2 ∷ CK20⁻ ∷ X2 ∷ Toff102 ∷ []) (Toff102 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ [])
  b0 = at 0 4 (Toff102 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) wn00239 ▸ done

-- pass [X2 CKd20 X2] [CS13]: 17 steps
lem-pass-X2-CKd20-X2-vs-CS13 : ⟪ (X2 ∷ CK20⁻ ∷ X2 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CKd20-X2-vs-CS13 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X2 ∷ CK20⁻ ∷ X2 ∷ CS13 ∷ []) (X2 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ CK10⁻ ∷ CS23 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ X2 ∷ [])
  b0 = at 2 2 (CS13 ∷ X2 ∷ []) wn00257 ▸
       at 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS23 ∷ Sw12 ∷ []) wn00020 ▸ done

  b1 : Chain (X2 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ CK10⁻ ∷ CS23 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ X2 ∷ []) (X2 ∷ CS13 ∷ CK20⁻ ∷ X2 ∷ [])
  b1 = at 4 2 (CS23 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (CS)) ▸
       at 3 2 (CS13 ∷ Sw12 ∷ []) wn00049 ▸
       at 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸
       at 3 5 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 1 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (X2 ∷ CS13 ∷ CK20⁻ ∷ X2 ∷ []) (CS13 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ [])
  b2 = at 0 2 (CS13 ∷ X2 ∷ []) wn00257 ▸ done

-- pass [X2 CKd20 X2] [CSd13]: 17 steps
lem-pass-X2-CKd20-X2-vs-CSd13 : ⟪ (X2 ∷ CK20⁻ ∷ X2 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CKd20-X2-vs-CSd13 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X2 ∷ CK20⁻ ∷ X2 ∷ CS13⁻ ∷ []) (X2 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ CK10⁻ ∷ CS23⁻ ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ X2 ∷ [])
  b0 = at 2 2 (CS13⁻ ∷ X2 ∷ []) wn00258 ▸
       at 2 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS23⁻ ∷ Sw12 ∷ []) wn00021 ▸ done

  b1 : Chain (X2 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ CK10⁻ ∷ CS23⁻ ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ X2 ∷ []) (X2 ∷ CS13⁻ ∷ CK20⁻ ∷ X2 ∷ [])
  b1 = at 4 2 (CS23⁻ ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) ((CS • CS • CS))) ▸
       at 3 2 (CS13⁻ ∷ Sw12 ∷ []) wn00051 ▸
       at 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸
       at 3 5 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 1 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (X2 ∷ CS13⁻ ∷ CK20⁻ ∷ X2 ∷ []) (CS13⁻ ∷ X2 ∷ CK20⁻ ∷ X2 ∷ [])
  b2 = at 0 2 (CS13⁻ ∷ X2 ∷ []) wn00258 ▸ done

-- pass [X2 CSd20 X2] [TOFF102]: 1 steps
lem-pass-X2-CSd20-X2-vs-TOFF102 : ⟪ (X2 ∷ CS02⁻ ∷ X2 ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CSd20-X2-vs-TOFF102 = run b0
  where
  b0 : Chain (X2 ∷ CS02⁻ ∷ X2 ∷ Toff102 ∷ []) (Toff102 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ [])
  b0 = at 0 4 (Toff102 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) wn00238 ▸ done

-- pass [X2 CSd20 X2] [CS13]: 17 steps
lem-pass-X2-CSd20-X2-vs-CS13 : ⟪ (X2 ∷ CS02⁻ ∷ X2 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CSd20-X2-vs-CS13 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X2 ∷ CS02⁻ ∷ X2 ∷ CS13 ∷ []) (X2 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ CS23 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ X2 ∷ [])
  b0 = at 2 2 (CS13 ∷ X2 ∷ []) wn00257 ▸
       at 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS23 ∷ Sw12 ∷ []) wn00020 ▸ done

  b1 : Chain (X2 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ CS23 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ X2 ∷ []) (X2 ∷ CS13 ∷ CS02⁻ ∷ X2 ∷ [])
  b1 = at 4 2 (CS23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (CS)) ▸
       at 3 2 (CS13 ∷ Sw12 ∷ []) wn00049 ▸
       at 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸
       at 3 5 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 1 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (X2 ∷ CS13 ∷ CS02⁻ ∷ X2 ∷ []) (CS13 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ [])
  b2 = at 0 2 (CS13 ∷ X2 ∷ []) wn00257 ▸ done

-- pass [X2 CSd20 X2] [CSd13]: 17 steps
lem-pass-X2-CSd20-X2-vs-CSd13 : ⟪ (X2 ∷ CS02⁻ ∷ X2 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CSd20-X2-vs-CSd13 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X2 ∷ CS02⁻ ∷ X2 ∷ CS13⁻ ∷ []) (X2 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ CS23⁻ ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ X2 ∷ [])
  b0 = at 2 2 (CS13⁻ ∷ X2 ∷ []) wn00258 ▸
       at 2 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS23⁻ ∷ Sw12 ∷ []) wn00021 ▸ done

  b1 : Chain (X2 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ CS23⁻ ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ X2 ∷ []) (X2 ∷ CS13⁻ ∷ CS02⁻ ∷ X2 ∷ [])
  b1 = at 4 2 (CS23⁻ ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) ((CS • CS • CS))) ▸
       at 3 2 (CS13⁻ ∷ Sw12 ∷ []) wn00051 ▸
       at 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸
       at 3 5 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 1 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (X2 ∷ CS13⁻ ∷ CS02⁻ ∷ X2 ∷ []) (CS13⁻ ∷ X2 ∷ CS02⁻ ∷ X2 ∷ [])
  b2 = at 0 2 (CS13⁻ ∷ X2 ∷ []) wn00258 ▸ done

-- pass [CCZ123] [CS13]: 1 steps
lem-pass-CCZ123-vs-CS13 : ⟪ (CCZ123 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-CS13 = run b0
  where
  b0 : Chain (CCZ123 ∷ CS13 ∷ []) (CS13 ∷ CCZ123 ∷ [])
  b0 = at 0 2 (CS13 ∷ CCZ123 ∷ []) wn00259 ▸ done

-- pass [CCZ123] [CSd13]: 1 steps
lem-pass-CCZ123-vs-CSd13 : ⟪ (CCZ123 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-CSd13 = run b0
  where
  b0 : Chain (CCZ123 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CCZ123 ∷ [])
  b0 = at 0 2 (CS13⁻ ∷ CCZ123 ∷ []) wn00260 ▸ done

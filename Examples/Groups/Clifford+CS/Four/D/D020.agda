{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D020 where

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
open import Examples.Groups.Clifford+CS.Four.Wins.W01 using (wn00001 ; wn00003 ; wn00005 ; wn00007 ; wn00008 ; wn00009 ; wn00010 ; wn00012 ; wn00014 ; wn00015 ; wn00016 ; wn00018 ; wn00019 ; wn00020 ; wn00022 ; wn00023 ; wn00024 ; wn00025 ; wn00027 ; wn00028 ; wn00029 ; wn00030 ; wn00031 ; wn00048 ; wn00049 ; wn00051 ; wn00056 ; wn00065 ; wn00074 ; wn00084 ; wn00118 ; wn00121 ; wn00122 ; wn00123 ; wn00124 ; wn00125 ; wn00127 ; wn00173 ; wn00175 ; wn00196 ; wn00215)
open import Examples.Groups.Clifford+CS.Four.Wins.W02 using (wn00216 ; wn00217 ; wn00218 ; wn00219 ; wn00220 ; wn00221 ; wn00222 ; wn00271 ; wn00272 ; wn00273 ; wn00274 ; wn00275 ; wn00280 ; wn00340 ; wn00359 ; wn00363 ; wn00366 ; wn00398 ; wn00399)

-- pass [X3 CK32 X3] [TOFF201 CS23 TOFF201 CSd23]: 712 steps
lem-pass-X3-CK32-X3-vs-TOFF201-CS23-TOFF201-CSd23 : ⟪ (X3 ∷ CK32 ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ CK32 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CK32-X3-vs-TOFF201-CS23-TOFF201-CSd23 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (trans (run b38) (trans (run b39) (trans (run b40) (trans (run b41) (trans (run b42) (trans (run b43) (trans (run b44) (trans (run b45) (trans (run b46) (trans (run b47) (trans (run b48) (trans (run b49) (trans (run b50) (trans (run b51) (trans (run b52) (trans (run b53) (trans (run b54) (trans (run b55) (trans (run b56) (trans (run b57) (trans (run b58) (trans (run b59) (trans (run b60) (trans (run b61) (trans (run b62) (trans (run b63) (trans (run b64) (trans (run b65) (trans (run b66) (trans (run b67) (trans (run b68) (trans (run b69) (trans (run b70) (trans (run b71) (trans (run b72) (trans (run b73) (trans (run b74) (trans (run b75) (trans (run b76) (trans (run b77) (trans (run b78) (trans (run b79) (trans (run b80) (trans (run b81) (trans (run b82) (trans (run b83) (trans (run b84) (trans (run b85) (trans (run b86) (trans (run b87) (run b88))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (X3 ∷ CK32 ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (X3 ∷ CK32 ∷ X3 ∷ Toff201 ∷ CS23 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw12 ∷ CX02 ∷ CS01 ∷ K1 ∷ ι ∷ Sw12 ∷ CS23⁻ ∷ [])
  b0 = at 6 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 5 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (Sw12 ∷ ι ∷ []) (low₁-comm (iI) (Swap)) ▸
       at 11 2 (Sw12 ∷ K1 ∷ []) wn00398 ▸
       at 10 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] wn00014 ▸
       at 9 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 10 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (X3 ∷ CK32 ∷ X3 ∷ Toff201 ∷ CS23 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw12 ∷ CX02 ∷ CS01 ∷ K1 ∷ ι ∷ Sw12 ∷ CS23⁻ ∷ []) (X3 ∷ CK32 ∷ X3 ∷ Toff201 ∷ Sw12 ∷ CS13 ∷ Toff102 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b1 = at 8 2 (Sw12 ∷ CS12⁻ ∷ []) wn00015 ▸
       at 7 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 8 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw12 ∷ CS12 ∷ []) wn00016 ▸
       at 5 2 (Sw12 ∷ K1 ∷ []) wn00398 ▸
       at 6 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) wn00366 ▸
       at 6 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw12 ∷ CS13 ∷ []) wn00048 ▸ done

  b2 : Chain (X3 ∷ CK32 ∷ X3 ∷ Toff201 ∷ Sw12 ∷ CS13 ∷ Toff102 ∷ Sw12 ∷ CS23⁻ ∷ []) (X3 ∷ CK32 ∷ X3 ∷ K2 ∷ CS12 ∷ CX01 ∷ Sw12 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K1 ∷ ι ∷ CS13 ∷ Toff102 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b2 = at 3 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw12 ∷ ι ∷ []) (low₁-comm (iI) (Swap)) ▸
       at 9 2 (Sw12 ∷ K1 ∷ []) wn00398 ▸
       at 8 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00014 ▸
       at 7 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 8 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw12 ∷ CS12⁻ ∷ []) wn00015 ▸ done

  b3 : Chain (X3 ∷ CK32 ∷ X3 ∷ K2 ∷ CS12 ∷ CX01 ∷ Sw12 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K1 ∷ ι ∷ CS13 ∷ Toff102 ∷ Sw12 ∷ CS23⁻ ∷ []) (X3 ∷ Sw12 ∷ CK31 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b3 = at 5 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 6 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw12 ∷ CS12 ∷ []) wn00016 ▸
       at 3 2 (Sw12 ∷ K1 ∷ []) wn00398 ▸
       at 4 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) wn00366 ▸
       at 4 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw12 ∷ X3 ∷ []) (sym (low₃-comm ((Swap ↑)) (X))) ▸
       at 1 2 (Sw12 ∷ CK31 ∷ []) wn00280 ▸ done

  b4 : Chain (X3 ∷ Sw12 ∷ CK31 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ X3 ∷ CK31 ∷ X3 ∷ Toff102 ∷ CS13 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b4 = at 0 2 (Sw12 ∷ X3 ∷ []) (sym (low₃-comm ((Swap ↑)) (X))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 12 2 (Sw23 ∷ K1 ∷ []) (low-comm ((K ↑)) (Swap)) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 12 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸ done

  b5 : Chain (Sw12 ∷ X3 ∷ CK31 ∷ X3 ∷ Toff102 ∷ CS13 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ X3 ∷ CK31 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Sw23 ∷ Sw23 ∷ K1 ∷ Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b5 = at 9 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 10 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 8 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw23 ∷ K1 ∷ []) (low-comm ((K ↑)) (Swap)) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 8 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸ done

  b6 : Chain (Sw12 ∷ X3 ∷ CK31 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Sw23 ∷ Sw23 ∷ K1 ∷ Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ X3 ∷ CK31 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Sw23 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b6 = at 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00003 ▸
       at 10 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 12 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] wn00003 ▸
       at 12 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 [] wn00003 ▸ done

  b7 : Chain (Sw12 ∷ X3 ∷ CK31 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Sw23 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ X3 ∷ CK31 ∷ X3 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ CS12 ∷ Toff103 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b7 = at 14 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 15 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 8 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) wn00196 ▸
       at 8 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 7 3 (Toff103 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00003 ▸
       at 4 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸ done

  b8 : Chain (Sw12 ∷ X3 ∷ CK31 ∷ X3 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ CS12 ∷ Toff103 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ X3 ∷ CK31 ∷ X3 ∷ K1 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ CS12 ∷ Toff103 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b8 = at 11 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 10 2 (Sw23 ∷ K1 ∷ []) (low-comm ((K ↑)) (Swap)) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 10 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 8 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸ done

  b9 : Chain (Sw12 ∷ X3 ∷ CK31 ∷ X3 ∷ K1 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ CS12 ∷ Toff103 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ X3 ∷ CK31 ∷ X3 ∷ Sw23 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ Sw23 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ CS12 ∷ Toff103 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b9 = at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw23 ∷ K1 ∷ []) (low-comm ((K ↑)) (Swap)) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00003 ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b10 : Chain (Sw12 ∷ X3 ∷ CK31 ∷ X3 ∷ Sw23 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ Sw23 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ CS12 ∷ Toff103 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ X3 ∷ CK31 ∷ X3 ∷ Sw23 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ CS12 ∷ Toff103 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b10 = at 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00003 ▸
       at 10 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] wn00003 ▸
       at 12 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 13 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 6 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) wn00196 ▸ done

  b11 : Chain (Sw12 ∷ X3 ∷ CK31 ∷ X3 ∷ Sw23 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ CS12 ∷ Toff103 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ Sw23 ∷ X2 ∷ CK21 ∷ X2 ∷ Toff103 ∷ CS12 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b11 = at 6 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (Toff103 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 2 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸
       at 1 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 8 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 7 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b12 : Chain (Sw12 ∷ Sw23 ∷ X2 ∷ CK21 ∷ X2 ∷ Toff103 ∷ CS12 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ Sw23 ∷ X2 ∷ CK21 ∷ X2 ∷ Toff103 ∷ CS12 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b12 = at 8 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 8 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 10 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b13 : Chain (Sw12 ∷ Sw23 ∷ X2 ∷ CK21 ∷ X2 ∷ Toff103 ∷ CS12 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ Sw23 ∷ X2 ∷ CK21 ∷ X2 ∷ Toff103 ∷ CS12 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ K0 ∷ ι1 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b13 = at 14 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 12 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 14 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 15 2 [] wn00003 ▸
       at 14 2 (Sw01 ∷ ι1 ∷ []) wn00127 ▸
       at 13 2 (Sw01 ∷ K0 ∷ []) wn00271 ▸
       at 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b14 : Chain (Sw12 ∷ Sw23 ∷ X2 ∷ CK21 ∷ X2 ∷ Toff103 ∷ CS12 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ K0 ∷ ι1 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ Sw23 ∷ X2 ∷ CK21 ∷ X2 ∷ Toff103 ∷ CS12 ∷ K1 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ Sw01 ∷ CS02⁻ ∷ Sw23 ∷ CX10 ∷ CS13 ∷ K0 ∷ ι1 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b14 = at 14 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 13 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 12 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 13 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 11 2 (Sw01 ∷ CS02⁻ ∷ []) wn00009 ▸ done

  b15 : Chain (Sw12 ∷ Sw23 ∷ X2 ∷ CK21 ∷ X2 ∷ Toff103 ∷ CS12 ∷ K1 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ Sw01 ∷ CS02⁻ ∷ Sw23 ∷ CX10 ∷ CS13 ∷ K0 ∷ ι1 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ Sw23 ∷ X2 ∷ CK21 ∷ X2 ∷ Toff103 ∷ CS12 ∷ K1 ∷ Sw01 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K0 ∷ ι1 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b15 = at 10 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 11 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 9 2 (Sw01 ∷ CS02 ∷ []) wn00010 ▸
       at 8 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b16 : Chain (Sw12 ∷ Sw23 ∷ X2 ∷ CK21 ∷ X2 ∷ Toff103 ∷ CS12 ∷ K1 ∷ Sw01 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K0 ∷ ι1 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ Sw23 ∷ X2 ∷ CK21 ∷ X2 ∷ Toff103 ∷ CS12 ∷ Sw01 ∷ Sw23 ∷ K0 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ Sw23 ∷ CX10 ∷ CS13 ∷ K0 ∷ ι1 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b16 = at 7 2 (Sw01 ∷ K0 ∷ []) wn00271 ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 9 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00003 ▸
       at 11 2 (CX10 ∷ Sw23 ∷ []) (sym (low-comm (CX₁₀) (Swap))) ▸
       at 13 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] wn00003 ▸ done

  b17 : Chain (Sw12 ∷ Sw23 ∷ X2 ∷ CK21 ∷ X2 ∷ Toff103 ∷ CS12 ∷ Sw01 ∷ Sw23 ∷ K0 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ Sw23 ∷ CX10 ∷ CS13 ∷ K0 ∷ ι1 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ Sw23 ∷ X2 ∷ CK21 ∷ X2 ∷ Toff103 ∷ CS12 ∷ Sw01 ∷ Toff013 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b17 = at 13 2 (CX10 ∷ Sw23 ∷ []) (sym (low-comm (CX₁₀) (Swap))) ▸
       at 15 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 [] wn00003 ▸
       at 15 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 16 2 (ι1 ∷ Sw23 ∷ []) (sym (low-comm ((iI ↑)) (Swap))) ▸
       at 9 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) wn00272 ▸
       at 9 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 8 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸ done

  b18 : Chain (Sw12 ∷ Sw23 ∷ X2 ∷ CK21 ∷ X2 ∷ Toff103 ∷ CS12 ∷ Sw01 ∷ Toff013 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ Sw23 ∷ X2 ∷ CK21 ∷ X2 ∷ K1 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw01 ∷ CS02 ∷ Toff013 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b18 = at 6 2 (Sw01 ∷ CS02 ∷ []) wn00010 ▸
       at 5 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b19 : Chain (Sw12 ∷ Sw23 ∷ X2 ∷ CK21 ∷ X2 ∷ K1 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw01 ∷ CS02 ∷ Toff013 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ Sw23 ∷ X2 ∷ CK21 ∷ X2 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ Sw01 ∷ ι1 ∷ CS02 ∷ Toff013 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b19 = at 8 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 10 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 12 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 13 2 [] wn00003 ▸
       at 12 2 (Sw01 ∷ ι1 ∷ []) wn00127 ▸ done

  b20 : Chain (Sw12 ∷ Sw23 ∷ X2 ∷ CK21 ∷ X2 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ Sw01 ∷ ι1 ∷ CS02 ∷ Toff013 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ Sw23 ∷ X2 ∷ CK21 ∷ X2 ∷ K1 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw01 ∷ CX10 ∷ CS13 ∷ K0 ∷ ι1 ∷ CS02 ∷ Toff013 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b20 = at 11 2 (Sw01 ∷ K0 ∷ []) wn00271 ▸
       at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 11 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 10 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 11 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b21 : Chain (Sw12 ∷ Sw23 ∷ X2 ∷ CK21 ∷ X2 ∷ K1 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw01 ∷ CX10 ∷ CS13 ∷ K0 ∷ ι1 ∷ CS02 ∷ Toff013 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ Sw23 ∷ X2 ∷ CK21 ∷ X2 ∷ K1 ∷ Sw23 ∷ Sw01 ∷ CS02 ∷ Sw23 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K0 ∷ ι1 ∷ CS02 ∷ Toff013 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b21 = at 10 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 9 2 (Sw01 ∷ CS02⁻ ∷ []) wn00009 ▸
       at 8 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 9 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 7 2 (Sw01 ∷ CS02 ∷ []) wn00010 ▸ done

  b22 : Chain (Sw12 ∷ Sw23 ∷ X2 ∷ CK21 ∷ X2 ∷ K1 ∷ Sw23 ∷ Sw01 ∷ CS02 ∷ Sw23 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K0 ∷ ι1 ∷ CS02 ∷ Toff013 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ Sw23 ∷ X2 ∷ CK21 ∷ X2 ∷ Sw01 ∷ Sw23 ∷ K0 ∷ CS02 ∷ CX10 ∷ Sw23 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K0 ∷ ι1 ∷ CS02 ∷ Toff013 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b22 = at 6 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw01 ∷ K0 ∷ []) wn00271 ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 7 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00003 ▸
       at 9 2 (CX10 ∷ Sw23 ∷ []) (sym (low-comm (CX₁₀) (Swap))) ▸ done

  b23 : Chain (Sw12 ∷ Sw23 ∷ X2 ∷ CK21 ∷ X2 ∷ Sw01 ∷ Sw23 ∷ K0 ∷ CS02 ∷ CX10 ∷ Sw23 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K0 ∷ ι1 ∷ CS02 ∷ Toff013 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ Sw23 ∷ X2 ∷ CK21 ∷ X2 ∷ Sw01 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b23 = at 11 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00003 ▸
       at 11 2 (CX10 ∷ Sw23 ∷ []) (sym (low-comm (CX₁₀) (Swap))) ▸
       at 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] wn00003 ▸
       at 13 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 14 2 (ι1 ∷ Sw23 ∷ []) (sym (low-comm ((iI ↑)) (Swap))) ▸
       at 7 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) wn00272 ▸ done

  b24 : Chain (Sw12 ∷ Sw23 ∷ X2 ∷ CK21 ∷ X2 ∷ Sw01 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ Sw23 ∷ Sw01 ∷ X2 ∷ CK20 ∷ X2 ∷ Toff013 ∷ CS02 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b24 = at 7 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 6 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 3 2 (Sw01 ∷ CK20 ∷ []) wn00273 ▸
       at 2 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 9 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 8 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸ done

  b25 : Chain (Sw12 ∷ Sw23 ∷ Sw01 ∷ X2 ∷ CK20 ∷ X2 ∷ Toff013 ∷ CS02 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ Sw23 ∷ Sw01 ∷ X2 ∷ CK20 ∷ X2 ∷ Toff013 ∷ CS02 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b25 = at 8 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 9 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 13 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 11 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 15 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b26 : Chain (Sw12 ∷ Sw23 ∷ Sw01 ∷ X2 ∷ CK20 ∷ X2 ∷ Toff013 ∷ CS02 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ Sw23 ∷ Sw01 ∷ X2 ∷ CK20 ∷ X2 ∷ Toff013 ∷ CS02 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b26 = at 13 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 15 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 16 2 [] wn00003 ▸
       at 15 2 (Sw12 ∷ ι ∷ []) (low₁-comm (iI) (Swap)) ▸
       at 14 2 (Sw12 ∷ K0 ∷ []) (low₁-comm (K) (Swap)) ▸
       at 13 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 16 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) wn00022 ▸ done

  b27 : Chain (Sw12 ∷ Sw23 ∷ Sw01 ∷ X2 ∷ CK20 ∷ X2 ∷ Toff013 ∷ CS02 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ Sw23 ∷ Sw01 ∷ X2 ∷ CK20 ∷ X2 ∷ Toff013 ∷ CS02 ∷ K0 ∷ CS13 ∷ Sw12 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b27 = at 15 2 (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap)) ▸
       at 13 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) wn00023 ▸
       at 14 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 12 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 13 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (Sw12 ∷ CS23⁻ ∷ []) wn00084 ▸
       at 10 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 11 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸ done

  b28 : Chain (Sw12 ∷ Sw23 ∷ Sw01 ∷ X2 ∷ CK20 ∷ X2 ∷ Toff013 ∷ CS02 ∷ K0 ∷ CS13 ∷ Sw12 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ Sw23 ∷ Sw01 ∷ X2 ∷ CK20 ∷ X2 ∷ Toff013 ∷ CS02 ∷ Sw12 ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b28 = at 9 2 (Sw12 ∷ CS23 ∷ []) wn00065 ▸
       at 8 2 (Sw12 ∷ K0 ∷ []) (low₁-comm (K) (Swap)) ▸
       at 9 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 10 2 (K1 ∷ Sw01 ∷ []) wn00123 ▸
       at 11 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 12 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 13 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 14 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸ done

  b29 : Chain (Sw12 ∷ Sw23 ∷ Sw01 ∷ X2 ∷ CK20 ∷ X2 ∷ Toff013 ∷ CS02 ∷ Sw12 ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ Sw23 ∷ Sw01 ∷ X2 ∷ CK20 ∷ X2 ∷ Toff013 ∷ CS02 ∷ Sw12 ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b29 = at 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 16 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 17 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 15 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 16 2 (K1 ∷ Sw01 ∷ []) wn00123 ▸
       at 17 2 (ι1 ∷ Sw01 ∷ []) wn00124 ▸
       at 10 8 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) wn00125 ▸ done

  b30 : Chain (Sw12 ∷ Sw23 ∷ Sw01 ∷ X2 ∷ CK20 ∷ X2 ∷ Toff013 ∷ CS02 ∷ Sw12 ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ Sw23 ∷ Sw01 ∷ X2 ∷ CK20 ∷ X2 ∷ K0 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Toff023 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b30 = at 10 8 (Toff123 ∷ []) (by-assoc Eq.refl) ▸
       at 9 3 (Toff023 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00014 ▸
       at 6 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b31 : Chain (Sw12 ∷ Sw23 ∷ Sw01 ∷ X2 ∷ CK20 ∷ X2 ∷ K0 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Toff023 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ Sw23 ∷ Sw01 ∷ X2 ∷ CK20 ∷ X2 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ Sw23 ∷ ι ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Toff023 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b31 = at 7 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 9 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 13 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 11 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸ done

  b32 : Chain (Sw12 ∷ Sw23 ∷ Sw01 ∷ X2 ∷ CK20 ∷ X2 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ Sw23 ∷ ι ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Toff023 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ Sw23 ∷ Sw01 ∷ X2 ∷ CK20 ∷ X2 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ K0 ∷ ι ∷ CS01 ∷ Toff023 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b32 = at 13 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 14 2 [] wn00003 ▸
       at 13 2 (Sw12 ∷ ι ∷ []) (low₁-comm (iI) (Swap)) ▸
       at 12 2 (Sw12 ∷ K0 ∷ []) (low₁-comm (K) (Swap)) ▸
       at 11 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 14 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) wn00022 ▸
       at 13 2 (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap)) ▸
       at 11 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) wn00023 ▸ done

  b33 : Chain (Sw12 ∷ Sw23 ∷ Sw01 ∷ X2 ∷ CK20 ∷ X2 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ K0 ∷ ι ∷ CS01 ∷ Toff023 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ Sw23 ∷ Sw01 ∷ X2 ∷ CK20 ∷ X2 ∷ Sw12 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ CS01 ∷ Toff023 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b33 = at 12 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 11 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw12 ∷ CS23⁻ ∷ []) wn00084 ▸
       at 8 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 9 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw12 ∷ CS23 ∷ []) wn00065 ▸
       at 6 2 (Sw12 ∷ K0 ∷ []) (low₁-comm (K) (Swap)) ▸ done

  b34 : Chain (Sw12 ∷ Sw23 ∷ Sw01 ∷ X2 ∷ CK20 ∷ X2 ∷ Sw12 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ CS01 ∷ Toff023 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ Sw23 ∷ Sw01 ∷ X2 ∷ CK20 ∷ X2 ∷ Sw12 ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ Sw01 ∷ CS02 ∷ Sw23 ∷ K0 ∷ ι ∷ CS01 ∷ Toff023 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b34 = at 7 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 8 2 (K1 ∷ Sw01 ∷ []) wn00123 ▸
       at 9 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 10 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 11 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 12 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b35 : Chain (Sw12 ∷ Sw23 ∷ Sw01 ∷ X2 ∷ CK20 ∷ X2 ∷ Sw12 ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ Sw01 ∷ CS02 ∷ Sw23 ∷ K0 ∷ ι ∷ CS01 ∷ Toff023 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ Sw23 ∷ Sw01 ∷ X2 ∷ CK20 ∷ X2 ∷ Sw12 ∷ Toff023 ∷ CS01 ∷ Toff023 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b35 = at 14 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 15 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 13 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 (K1 ∷ Sw01 ∷ []) wn00123 ▸
       at 15 2 (ι1 ∷ Sw01 ∷ []) wn00124 ▸
       at 8 8 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) wn00125 ▸
       at 8 8 (Toff123 ∷ []) (by-assoc Eq.refl) ▸
       at 7 3 (Toff023 ∷ []) (by-assoc Eq.refl) ▸ done

  b36 : Chain (Sw12 ∷ Sw23 ∷ Sw01 ∷ X2 ∷ CK20 ∷ X2 ∷ Sw12 ∷ Toff023 ∷ CS01 ∷ Toff023 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ X1 ∷ CK10 ∷ X1 ∷ Toff023 ∷ CS01 ∷ K0 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b36 = at 5 2 (Sw12 ∷ X1 ∷ []) wn00215 ▸
       at 4 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00014 ▸
       at 3 2 (Sw12 ∷ X1 ∷ []) wn00215 ▸
       at 10 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 9 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 10 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸ done

  b37 : Chain (Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ X1 ∷ CK10 ∷ X1 ∷ Toff023 ∷ CS01 ∷ K0 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ X1 ∷ CK10 ∷ X1 ∷ Toff023 ∷ CS01 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b37 = at 10 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 11 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 12 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 13 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 15 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 15 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 16 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b38 : Chain (Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ X1 ∷ CK10 ∷ X1 ∷ Toff023 ∷ CS01 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ X1 ∷ CK10 ∷ X1 ∷ Toff023 ∷ CS01 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b38 = at 14 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 16 2 (ι ∷ Sw01 ∷ []) wn00122 ▸
       at 17 2 [] wn00031 ▸
       at 16 2 (Sw01 ∷ ι1 ∷ []) wn00127 ▸
       at 15 2 (Sw01 ∷ K1 ∷ []) wn00118 ▸
       at 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 16 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b39 : Chain (Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ X1 ∷ CK10 ∷ X1 ∷ Toff023 ∷ CS01 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ X1 ∷ CK10 ∷ X1 ∷ Toff023 ∷ CS01 ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b39 = at 15 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 14 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 15 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸
       at 12 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 11 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸
       at 10 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 9 2 (Sw01 ∷ K1 ∷ []) wn00118 ▸ done

  b40 : Chain (Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ X1 ∷ CK10 ∷ X1 ∷ Toff023 ∷ CS01 ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ X1 ∷ CK10 ∷ X1 ∷ K0 ∷ CS23 ∷ CX02 ∷ Sw01 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ CS01 ∷ Toff123 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b40 = at 10 8 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) wn00125 ▸
       at 10 8 (Toff123 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw01 ∷ CS01 ∷ []) wn00216 ▸
       at 7 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 8 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 8 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 9 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸ done

  b41 : Chain (Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ X1 ∷ CK10 ∷ X1 ∷ K0 ∷ CS23 ∷ CX02 ∷ Sw01 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ CS01 ∷ Toff123 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ X1 ∷ CK10 ∷ X1 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ Sw01 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ CS01 ∷ Toff123 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b41 = at 10 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 11 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 13 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 14 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 12 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸ done

  b42 : Chain (Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ X1 ∷ CK10 ∷ X1 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ Sw01 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ CS01 ∷ Toff123 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ X1 ∷ CK10 ∷ X1 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ K1 ∷ ι1 ∷ CS01 ∷ Toff123 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b42 = at 14 2 (ι ∷ Sw01 ∷ []) wn00122 ▸
       at 15 2 [] wn00031 ▸
       at 14 2 (Sw01 ∷ ι1 ∷ []) wn00127 ▸
       at 13 2 (Sw01 ∷ K1 ∷ []) wn00118 ▸
       at 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 13 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 12 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b43 : Chain (Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ X1 ∷ CK10 ∷ X1 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ K1 ∷ ι1 ∷ CS01 ∷ Toff123 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ X1 ∷ CK10 ∷ X1 ∷ Sw01 ∷ Toff123 ∷ CS01 ∷ Toff123 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b43 = at 13 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸
       at 10 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 9 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸
       at 8 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 7 2 (Sw01 ∷ K1 ∷ []) wn00118 ▸
       at 8 8 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) wn00125 ▸
       at 8 8 (Toff123 ∷ []) (by-assoc Eq.refl) ▸ done

  b44 : Chain (Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ X1 ∷ CK10 ∷ X1 ∷ Sw01 ∷ Toff123 ∷ CS01 ∷ Toff123 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ K0 ∷ CS23 ∷ CX02 ∷ Sw01 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ CS01 ∷ Toff123 ∷ X0 ∷ CK01 ∷ X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b44 = at 6 2 (Sw01 ∷ X0 ∷ []) wn00217 ▸
       at 5 2 (Sw01 ∷ CK01 ∷ []) wn00218 ▸
       at 4 2 (Sw01 ∷ X0 ∷ []) wn00217 ▸
       at 5 6 (Toff123 ∷ CS01 ∷ Toff123 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (ax ck-tct) ▸
       at 5 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 5 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 6 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸ done

  b45 : Chain (Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ K0 ∷ CS23 ∷ CX02 ∷ Sw01 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ CS01 ∷ Toff123 ∷ X0 ∷ CK01 ∷ X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ Sw01 ∷ ι1 ∷ CS01 ∷ Toff123 ∷ X0 ∷ CK01 ∷ X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b45 = at 7 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 8 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸ done

  b46 : Chain (Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ Sw01 ∷ ι1 ∷ CS01 ∷ Toff123 ∷ X0 ∷ CK01 ∷ X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw01 ∷ CS01 ∷ Toff123 ∷ X0 ∷ CK01 ∷ X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b46 = at 11 2 (ι ∷ Sw01 ∷ []) wn00122 ▸
       at 4 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 5 2 (K1 ∷ Sw01 ∷ []) wn00123 ▸
       at 6 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 7 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 8 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 9 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b47 : Chain (Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw01 ∷ CS01 ∷ Toff123 ∷ X0 ∷ CK01 ∷ X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Toff123 ∷ Sw01 ∷ Sw01 ∷ CS01 ∷ Toff123 ∷ X0 ∷ CK01 ∷ X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b47 = at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 11 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 12 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (K1 ∷ Sw01 ∷ []) wn00123 ▸
       at 12 2 (ι1 ∷ Sw01 ∷ []) wn00124 ▸
       at 5 8 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) wn00125 ▸
       at 5 8 (Toff123 ∷ []) (by-assoc Eq.refl) ▸ done

  b48 : Chain (Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Toff123 ∷ Sw01 ∷ Sw01 ∷ CS01 ∷ Toff123 ∷ X0 ∷ CK01 ∷ X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Toff023 ∷ CS01 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ K1 ∷ ι1 ∷ X0 ∷ CK01 ∷ X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b48 = at 4 3 (Toff023 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS01 ∷ Sw01 ∷ []) wn00219 ▸
       at 7 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 7 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 8 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 9 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 10 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸ done

  b49 : Chain (Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Toff023 ∷ CS01 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ K1 ∷ ι1 ∷ X0 ∷ CK01 ∷ X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Toff023 ∷ CS01 ∷ Sw01 ∷ Sw01 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ Sw01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b49 = at 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 12 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 13 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 11 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 13 2 (ι ∷ Sw01 ∷ []) wn00122 ▸
       at 6 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸ done

  b50 : Chain (Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Toff023 ∷ CS01 ∷ Sw01 ∷ Sw01 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ Sw01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Toff023 ∷ CS01 ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ CS12 ∷ Sw01 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b50 = at 7 2 (K1 ∷ Sw01 ∷ []) wn00123 ▸
       at 8 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 9 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 10 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 11 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 13 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸ done

  b51 : Chain (Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Toff023 ∷ CS01 ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ CS12 ∷ Sw01 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Toff023 ∷ CS01 ∷ Toff023 ∷ X1 ∷ Sw01 ∷ CK01 ∷ X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b51 = at 14 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 12 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (K1 ∷ Sw01 ∷ []) wn00123 ▸
       at 14 2 (ι1 ∷ Sw01 ∷ []) wn00124 ▸
       at 7 8 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) wn00125 ▸
       at 7 8 (Toff123 ∷ []) (by-assoc Eq.refl) ▸
       at 6 3 (Toff023 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (X1 ∷ Sw01 ∷ []) wn00220 ▸ done

  b52 : Chain (Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Toff023 ∷ CS01 ∷ Toff023 ∷ X1 ∷ Sw01 ∷ CK01 ∷ X0 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ K0 ∷ CS23 ∷ CX02 ∷ Sw01 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ CS01 ∷ Toff023 ∷ X1 ∷ CK10 ∷ X1 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b52 = at 8 2 (CK10 ∷ Sw01 ∷ []) wn00221 ▸
       at 9 2 (X1 ∷ Sw01 ∷ []) wn00220 ▸
       at 10 2 [] wn00031 ▸
       at 4 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 5 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 6 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸ done

  b53 : Chain (Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ K0 ∷ CS23 ∷ CX02 ∷ Sw01 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ CS01 ∷ Toff023 ∷ X1 ∷ CK10 ∷ X1 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ Sw01 ∷ ι1 ∷ Sw01 ∷ CS01 ∷ Toff023 ∷ X1 ∷ CK10 ∷ X1 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b53 = at 7 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 8 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸ done

  b54 : Chain (Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ Sw01 ∷ ι1 ∷ Sw01 ∷ CS01 ∷ Toff023 ∷ X1 ∷ CK10 ∷ X1 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ Sw23 ∷ Sw01 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw12 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ CS03 ∷ K0 ∷ ι ∷ CS01 ∷ Toff023 ∷ X1 ∷ CK10 ∷ X1 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b54 = at 11 2 (ι ∷ Sw01 ∷ []) wn00122 ▸
       at 12 2 [] wn00031 ▸
       at 3 2 (K0 ∷ Sw12 ∷ []) (sym (low₁-comm (K) (Swap))) ▸
       at 4 2 (CS13 ∷ Sw12 ∷ []) wn00049 ▸
       at 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00014 ▸
       at 6 2 (CS13⁻ ∷ Sw12 ∷ []) wn00051 ▸
       at 8 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸ done

  b55 : Chain (Sw12 ∷ Sw23 ∷ Sw01 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw12 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ CS03 ∷ K0 ∷ ι ∷ CS01 ∷ Toff023 ∷ X1 ∷ CK10 ∷ X1 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ Sw23 ∷ Sw01 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw12 ∷ CS01 ∷ Toff023 ∷ X1 ∷ CK10 ∷ X1 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b55 = at 7 2 [] wn00014 ▸
       at 9 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) wn00022 ▸
       at 10 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 11 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) wn00023 ▸
       at 8 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K0 ∷ Sw12 ∷ []) (sym (low₁-comm (K) (Swap))) ▸
       at 10 2 (ι ∷ Sw12 ∷ []) (sym (low₁-comm (iI) (Swap))) ▸ done

  b56 : Chain (Sw12 ∷ Sw23 ∷ Sw01 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw12 ∷ CS01 ∷ Toff023 ∷ X1 ∷ CK10 ∷ X1 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ CS03 ∷ K0 ∷ ι ∷ Sw12 ∷ CS01 ∷ Toff023 ∷ X1 ∷ CK10 ∷ X1 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b56 = at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00003 ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b57 : Chain (Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ CS03 ∷ K0 ∷ ι ∷ Sw12 ∷ CS01 ∷ Toff023 ∷ X1 ∷ CK10 ∷ X1 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ Sw23 ∷ Sw01 ∷ Toff013 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw12 ∷ Toff023 ∷ X1 ∷ CK10 ∷ X1 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b57 = at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00003 ▸
       at 10 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 11 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 4 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) wn00056 ▸
       at 4 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸ done

  b58 : Chain (Sw12 ∷ Sw23 ∷ Sw01 ∷ Toff013 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw12 ∷ Toff023 ∷ X1 ∷ CK10 ∷ X1 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ Sw23 ∷ Sw01 ∷ Toff013 ∷ CS02 ∷ Sw12 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ X1 ∷ CK10 ∷ X1 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b58 = at 4 3 (CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 7 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 8 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 9 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 10 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸ done

  b59 : Chain (Sw12 ∷ Sw23 ∷ Sw01 ∷ Toff013 ∷ CS02 ∷ Sw12 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ X1 ∷ CK10 ∷ X1 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ Sw23 ∷ Sw01 ∷ Toff013 ∷ CS02 ∷ Sw12 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ X1 ∷ CK10 ∷ X1 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b59 = at 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 12 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 13 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 11 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 13 2 (ι ∷ Sw01 ∷ []) wn00122 ▸
       at 14 2 [] wn00031 ▸ done

  b60 : Chain (Sw12 ∷ Sw23 ∷ Sw01 ∷ Toff013 ∷ CS02 ∷ Sw12 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ X1 ∷ CK10 ∷ X1 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ Sw23 ∷ Sw01 ∷ Toff013 ∷ CS02 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ K0 ∷ ι ∷ X1 ∷ CK10 ∷ X1 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b60 = at 5 2 (K0 ∷ Sw12 ∷ []) (sym (low₁-comm (K) (Swap))) ▸
       at 6 2 (CS13 ∷ Sw12 ∷ []) wn00049 ▸
       at 8 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00014 ▸
       at 8 2 (CS13⁻ ∷ Sw12 ∷ []) wn00051 ▸
       at 10 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00014 ▸
       at 11 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b61 : Chain (Sw12 ∷ Sw23 ∷ Sw01 ∷ Toff013 ∷ CS02 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ K0 ∷ ι ∷ X1 ∷ CK10 ∷ X1 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ Sw23 ∷ Sw01 ∷ Toff013 ∷ CS02 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw12 ∷ X1 ∷ CK10 ∷ X1 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b61 = at 10 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) wn00022 ▸
       at 12 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 13 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) wn00023 ▸
       at 10 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (K0 ∷ Sw12 ∷ []) (sym (low₁-comm (K) (Swap))) ▸
       at 12 2 (ι ∷ Sw12 ∷ []) (sym (low₁-comm (iI) (Swap))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸ done

  b62 : Chain (Sw12 ∷ Sw23 ∷ Sw01 ∷ Toff013 ∷ CS02 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw12 ∷ X1 ∷ CK10 ∷ X1 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ Sw23 ∷ Sw01 ∷ Toff013 ∷ CS02 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw12 ∷ X1 ∷ CK10 ∷ X1 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b62 = at 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00003 ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00003 ▸
       at 10 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] wn00003 ▸ done

  b63 : Chain (Sw12 ∷ Sw23 ∷ Sw01 ∷ Toff013 ∷ CS02 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw12 ∷ X1 ∷ CK10 ∷ X1 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ Sw23 ∷ Sw01 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ X2 ∷ CK20 ∷ Sw12 ∷ X1 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b63 = at 12 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 13 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 6 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) wn00056 ▸
       at 6 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (X2 ∷ Sw12 ∷ []) wn00222 ▸
       at 9 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 7 3 (CK20 ∷ []) (by-assoc Eq.refl) ▸ done

  b64 : Chain (Sw12 ∷ Sw23 ∷ Sw01 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ X2 ∷ CK20 ∷ Sw12 ∷ X1 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ Sw23 ∷ Sw01 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ X2 ∷ CK20 ∷ X2 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b64 = at 8 2 (X2 ∷ Sw12 ∷ []) wn00222 ▸
       at 9 2 [] wn00014 ▸
       at 3 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b65 : Chain (Sw12 ∷ Sw23 ∷ Sw01 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ X2 ∷ CK20 ∷ X2 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ Sw23 ∷ Sw01 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ CS02 ∷ Toff013 ∷ X2 ∷ CK20 ∷ X2 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b65 = at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 10 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 11 2 [] wn00003 ▸ done

  b66 : Chain (Sw12 ∷ Sw23 ∷ Sw01 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ CS02 ∷ Toff013 ∷ X2 ∷ CK20 ∷ X2 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ Sw23 ∷ K1 ∷ CS03 ∷ CX10 ∷ Sw01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ CS02 ∷ Toff013 ∷ X2 ∷ CK20 ∷ X2 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b66 = at 2 2 (K1 ∷ Sw01 ∷ []) wn00123 ▸
       at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 4 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 3 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX10 ∷ Sw01 ∷ []) wn00028 ▸
       at 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b67 : Chain (Sw12 ∷ Sw23 ∷ K1 ∷ CS03 ∷ CX10 ∷ Sw01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ CS02 ∷ Toff013 ∷ X2 ∷ CK20 ∷ X2 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ Sw23 ∷ K1 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ Sw23 ∷ CS12 ∷ Sw01 ∷ Sw23 ∷ K0 ∷ ι ∷ CS02 ∷ Toff013 ∷ X2 ∷ CK20 ∷ X2 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b67 = at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX10 ∷ Sw01 ∷ []) wn00028 ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸ done

  b68 : Chain (Sw12 ∷ Sw23 ∷ K1 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ Sw23 ∷ CS12 ∷ Sw01 ∷ Sw23 ∷ K0 ∷ ι ∷ CS02 ∷ Toff013 ∷ X2 ∷ CK20 ∷ X2 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ Sw23 ∷ Sw23 ∷ K1 ∷ CS02 ∷ Sw23 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ CS02 ∷ Toff013 ∷ X2 ∷ CK20 ∷ X2 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b68 = at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K1 ∷ Sw01 ∷ []) wn00123 ▸
       at 9 2 (ι1 ∷ Sw01 ∷ []) wn00124 ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸ done

  b69 : Chain (Sw12 ∷ Sw23 ∷ Sw23 ∷ K1 ∷ CS02 ∷ Sw23 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ CS02 ∷ Toff013 ∷ X2 ∷ CK20 ∷ X2 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ Sw23 ∷ Sw23 ∷ K1 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K1 ∷ ι1 ∷ Sw23 ∷ Sw01 ∷ CS02 ∷ Toff013 ∷ X2 ∷ CK20 ∷ X2 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b69 = at 5 2 (CX10 ∷ Sw23 ∷ []) (sym (low-comm (CX₁₀) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸
       at 7 2 (CX10 ∷ Sw23 ∷ []) (sym (low-comm (CX₁₀) (Swap))) ▸
       at 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00003 ▸
       at 9 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 10 2 (ι1 ∷ Sw23 ∷ []) (sym (low-comm ((iI ↑)) (Swap))) ▸ done

  b70 : Chain (Sw12 ∷ Sw23 ∷ Sw23 ∷ K1 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K1 ∷ ι1 ∷ Sw23 ∷ Sw01 ∷ CS02 ∷ Toff013 ∷ X2 ∷ CK20 ∷ X2 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ Sw23 ∷ Toff103 ∷ CS12 ∷ Sw01 ∷ K0 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ X2 ∷ CK20 ∷ X2 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b70 = at 3 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) wn00274 ▸
       at 3 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff103 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 5 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b71 : Chain (Sw12 ∷ Sw23 ∷ Toff103 ∷ CS12 ∷ Sw01 ∷ K0 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ X2 ∷ CK20 ∷ X2 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ Sw23 ∷ Toff103 ∷ CS12 ∷ Sw01 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ Sw23 ∷ ι ∷ Sw23 ∷ X2 ∷ CK20 ∷ X2 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b71 = at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 8 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 10 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸ done

  b72 : Chain (Sw12 ∷ Sw23 ∷ Toff103 ∷ CS12 ∷ Sw01 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ Sw23 ∷ ι ∷ Sw23 ∷ X2 ∷ CK20 ∷ X2 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ Sw23 ∷ Toff103 ∷ CS12 ∷ K1 ∷ CS03 ∷ Sw01 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ X2 ∷ CK20 ∷ X2 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b72 = at 12 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 13 2 [] wn00003 ▸
       at 4 2 (K1 ∷ Sw01 ∷ []) wn00123 ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b73 : Chain (Sw12 ∷ Sw23 ∷ Toff103 ∷ CS12 ∷ K1 ∷ CS03 ∷ Sw01 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ X2 ∷ CK20 ∷ X2 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ Sw23 ∷ Toff103 ∷ CS12 ∷ K1 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ Sw01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ K0 ∷ ι ∷ X2 ∷ CK20 ∷ X2 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b73 = at 6 2 (CX10 ∷ Sw01 ∷ []) wn00028 ▸
       at 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX10 ∷ Sw01 ∷ []) wn00028 ▸
       at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b74 : Chain (Sw12 ∷ Sw23 ∷ Toff103 ∷ CS12 ∷ K1 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ Sw01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ K0 ∷ ι ∷ X2 ∷ CK20 ∷ X2 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ Sw23 ∷ Toff103 ∷ CS12 ∷ Sw23 ∷ K1 ∷ Sw23 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ X2 ∷ CK20 ∷ X2 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b74 = at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (K1 ∷ Sw01 ∷ []) wn00123 ▸
       at 11 2 (ι1 ∷ Sw01 ∷ []) wn00124 ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸ done

  b75 : Chain (Sw12 ∷ Sw23 ∷ Toff103 ∷ CS12 ∷ Sw23 ∷ K1 ∷ Sw23 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ X2 ∷ CK20 ∷ X2 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ Sw23 ∷ Toff103 ∷ CS12 ∷ Sw23 ∷ K1 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Sw23 ∷ K1 ∷ ι1 ∷ Sw01 ∷ X2 ∷ CK20 ∷ X2 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b75 = at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸
       at 7 2 (CX10 ∷ Sw23 ∷ []) (sym (low-comm (CX₁₀) (Swap))) ▸
       at 9 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00003 ▸
       at 9 2 (CX10 ∷ Sw23 ∷ []) (sym (low-comm (CX₁₀) (Swap))) ▸
       at 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00003 ▸ done

  b76 : Chain (Sw12 ∷ Sw23 ∷ Toff103 ∷ CS12 ∷ Sw23 ∷ K1 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Sw23 ∷ K1 ∷ ι1 ∷ Sw01 ∷ X2 ∷ CK20 ∷ X2 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ Sw23 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ X2 ∷ CK21 ∷ X2 ∷ Sw01 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b76 = at 11 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 12 2 (ι1 ∷ Sw23 ∷ []) (sym (low-comm ((iI ↑)) (Swap))) ▸
       at 5 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) wn00274 ▸
       at 5 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 4 3 (Toff103 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 6 2 (CK21 ∷ Sw01 ∷ []) wn00275 ▸
       at 7 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸ done

  b77 : Chain (Sw12 ∷ Sw23 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ X2 ∷ CK21 ∷ X2 ∷ Sw01 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ Sw23 ∷ K1 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ CS12 ∷ Toff103 ∷ X2 ∷ CK21 ∷ X2 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b77 = at 8 2 [] wn00031 ▸
       at 2 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b78 : Chain (Sw12 ∷ Sw23 ∷ K1 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ CS12 ∷ Toff103 ∷ X2 ∷ CK21 ∷ X2 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ K1 ∷ Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ CS12 ∷ Toff103 ∷ X2 ∷ CK21 ∷ X2 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b78 = at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 10 2 [] wn00003 ▸
       at 1 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸ done

  b79 : Chain (Sw12 ∷ K1 ∷ Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ CS12 ∷ Toff103 ∷ X2 ∷ CK21 ∷ X2 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ K1 ∷ ι ∷ CS12 ∷ Toff103 ∷ X2 ∷ CK21 ∷ X2 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b79 = at 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸ done

  b80 : Chain (Sw12 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ K1 ∷ ι ∷ CS12 ∷ Toff103 ∷ X2 ∷ CK21 ∷ X2 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ Toff102 ∷ CS13 ∷ Sw23 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ X2 ∷ CK21 ∷ X2 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b80 = at 7 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 1 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) wn00196 ▸
       at 1 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸ done

  b81 : Chain (Sw12 ∷ Toff102 ∷ CS13 ∷ Sw23 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ X2 ∷ CK21 ∷ X2 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ Toff102 ∷ CS13 ∷ Sw23 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ K1 ∷ ι ∷ Sw23 ∷ X2 ∷ CK21 ∷ X2 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b81 = at 4 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 7 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b82 : Chain (Sw12 ∷ Toff102 ∷ CS13 ∷ Sw23 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ K1 ∷ ι ∷ Sw23 ∷ X2 ∷ CK21 ∷ X2 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ Toff102 ∷ CS13 ∷ K1 ∷ CS12 ∷ CX01 ∷ Sw23 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ X2 ∷ CK21 ∷ X2 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b82 = at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 11 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 12 2 [] wn00003 ▸
       at 3 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b83 : Chain (Sw12 ∷ Toff102 ∷ CS13 ∷ K1 ∷ CS12 ∷ CX01 ∷ Sw23 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ X2 ∷ CK21 ∷ X2 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (Sw12 ∷ Toff102 ∷ CS13 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ X2 ∷ CK21 ∷ X2 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b83 = at 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00003 ▸
       at 9 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 10 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 3 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) wn00196 ▸ done

  b84 : Chain (Sw12 ∷ Toff102 ∷ CS13 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ X2 ∷ CK21 ∷ X2 ∷ Sw23 ∷ Sw12 ∷ CS23⁻ ∷ []) (K2 ∷ Sw12 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ CS13 ∷ Toff102 ∷ X3 ∷ CK31 ∷ X3 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b84 = at 3 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 3 (CK31 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 7 2 [] wn00003 ▸
       at 1 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (K2 ∷ Sw12 ∷ []) wn00340 ▸ done

  b85 : Chain (K2 ∷ Sw12 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ CS13 ∷ Toff102 ∷ X3 ∷ CK31 ∷ X3 ∷ Sw12 ∷ CS23⁻ ∷ []) (K2 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ Sw12 ∷ K1 ∷ ι ∷ CS13 ∷ Toff102 ∷ X3 ∷ CK31 ∷ X3 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b85 = at 1 2 (CS12 ∷ Sw12 ∷ []) wn00018 ▸
       at 4 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 2 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS12⁻ ∷ Sw12 ∷ []) wn00019 ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00014 ▸ done

  b86 : Chain (K2 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ Sw12 ∷ K1 ∷ ι ∷ CS13 ∷ Toff102 ∷ X3 ∷ CK31 ∷ X3 ∷ Sw12 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ K2 ∷ CS12 ∷ Sw12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ X3 ∷ CK31 ∷ X3 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b86 = at 6 2 (K2 ∷ Sw12 ∷ []) wn00340 ▸
       at 7 2 (ι ∷ Sw12 ∷ []) (sym (low₁-comm (iI) (Swap))) ▸
       at 0 8 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) wn00363 ▸
       at 0 8 (Toff201 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (CS23 ∷ Sw12 ∷ []) wn00020 ▸
       at 3 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (K2 ∷ Sw12 ∷ []) wn00340 ▸
       at 3 2 (CS12 ∷ Sw12 ∷ []) wn00018 ▸ done

  b87 : Chain (Toff201 ∷ CS23 ∷ K2 ∷ CS12 ∷ Sw12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ X3 ∷ CK31 ∷ X3 ∷ Sw12 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ K2 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K2 ∷ Sw12 ∷ ι ∷ X3 ∷ CK31 ∷ X3 ∷ Sw12 ∷ CS23⁻ ∷ [])
  b87 = at 6 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS12⁻ ∷ Sw12 ∷ []) wn00019 ▸
       at 8 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 6 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 8 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00014 ▸
       at 8 2 (K2 ∷ Sw12 ∷ []) wn00340 ▸ done

  b88 : Chain (Toff201 ∷ CS23 ∷ K2 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K2 ∷ Sw12 ∷ ι ∷ X3 ∷ CK31 ∷ X3 ∷ Sw12 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ CK32 ∷ X3 ∷ [])
  b88 = at 9 2 (ι ∷ Sw12 ∷ []) (sym (low₁-comm (iI) (Swap))) ▸
       at 2 8 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) wn00363 ▸
       at 2 8 (Toff201 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (X3 ∷ Sw12 ∷ []) (low₃-comm ((Swap ↑)) (X)) ▸
       at 4 2 (CK32 ∷ Sw12 ∷ []) wn00359 ▸
       at 5 2 (X3 ∷ Sw12 ∷ []) (low₃-comm ((Swap ↑)) (X)) ▸
       at 6 2 [] wn00014 ▸
       at 3 4 (CS23⁻ ∷ X3 ∷ CK32 ∷ X3 ∷ []) wn00399 ▸ done

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D646 where

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
open import Examples.Groups.Clifford+CS.Four.Wins.W01 using (wn00001 ; wn00003 ; wn00005 ; wn00012 ; wn00014 ; wn00015 ; wn00016 ; wn00020 ; wn00021 ; wn00022 ; wn00023 ; wn00024 ; wn00025 ; wn00026 ; wn00027 ; wn00030 ; wn00031 ; wn00033 ; wn00043 ; wn00045 ; wn00046 ; wn00047 ; wn00048 ; wn00049 ; wn00050 ; wn00051 ; wn00052 ; wn00056 ; wn00071 ; wn00072 ; wn00073)
open import Examples.Groups.Clifford+CS.Four.Wins.W38 using (wn01882 ; wn01883)
open import Examples.Groups.Clifford+CS.Four.D.D380 using (lem-pass-CS03-vs-CZ23 ; lem-pass-CSd03-vs-CZ23)
open import Examples.Groups.Clifford+CS.Four.D.D445 using (lem-pass-CCZ023-vs-CS02 ; lem-pass-CCZ023-vs-CSd02)
open import Examples.Groups.Clifford+CS.Four.D.D510 using (lem-pass-CCZ123-vs-CSd03)
open import Examples.Groups.Clifford+CS.Four.D.D511 using (lem-pass-CCZ123-vs-CS03)
open import Examples.Groups.Clifford+CS.Four.D.D534 using (lem-pass-CCZ123-vs-CS02)
open import Examples.Groups.Clifford+CS.Four.D.D588 using (lem-pass-TOFF012-vs-CZ23)
open import Examples.Groups.Clifford+CS.Four.D.D596 using (lem-pass-CCZ123-vs-TOFF012)
open import Examples.Groups.Clifford+CS.Four.D.D597 using (lem-pass-CCZ123-vs-TOFF013)

-- pass [CCZ023] [TOFF013 CS02 TOFF013 CSd02]: 619 steps
lem-pass-CCZ023-vs-TOFF013-CS02-TOFF013-CSd02 : ⟪ (CCZ023 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ CCZ023 ∷ []) ⟫ʷ
lem-pass-CCZ023-vs-TOFF013-CS02-TOFF013-CSd02 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (trans (run b38) (trans (run b39) (trans (run b40) (trans (run b41) (trans (run b42) (trans (run b43) (trans (run b44) (trans (run b45) (trans (run b46) (trans (run b47) (trans (run b48) (trans (run b49) (trans (run b50) (trans (run b51) (trans (run b52) (trans (run b53) (trans (run b54) (trans (run b55) (trans (run b56) (trans (run b57) (trans (run b58) (trans (run b59) (trans (run b60) (trans (run b61) (trans (run b62) (trans (run b63) (trans (run b64) (trans (run b65) (trans (run b66) (trans (run b67) (trans (run b68) (trans (run b69) (trans (run b70) (trans (run b71) (trans (run b72) (trans (run b73) (trans (run b74) (trans (run b75) (trans (run b76) (run b77)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (CCZ023 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Toff012 ∷ Sw23 ∷ CCZ023 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 0 (Toff012 ∷ Toff012 ∷ []) wn00045 ▸
       at 1 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b1 : Chain (K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Toff012 ∷ Sw23 ∷ CCZ023 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (Sw23 ∷ K0 ∷ Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ CCZ023 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ [])
  b1 = at 3 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 7 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸ done

  b2 : Chain (Sw23 ∷ K0 ∷ Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ CCZ023 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ CCZ023 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ [])
  b2 = at 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸ done

  b3 : Chain (Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ CCZ023 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (Toff013 ∷ K0 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ CCZ023 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ [])
  b3 = at 7 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 1 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) wn00056 ▸
       at 1 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b4 : Chain (Toff013 ∷ K0 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ CCZ023 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (Toff013 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ Sw23 ∷ ι ∷ Sw23 ∷ CCZ023 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ [])
  b4 = at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸ done

  b5 : Chain (Toff013 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ Sw23 ∷ ι ∷ Sw23 ∷ CCZ023 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (Toff013 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ CCZ023 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ [])
  b5 = at 8 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸ done

  b6 : Chain (Toff013 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ CCZ023 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (Toff013 ∷ Toff013 ∷ Sw23 ∷ Sw23 ∷ CCZ023 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ [])
  b6 = at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00003 ▸
       at 8 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 2 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) wn00056 ▸
       at 2 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸ done

  b7 : Chain (Toff013 ∷ Toff013 ∷ Sw23 ∷ Sw23 ∷ CCZ023 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (Toff013 ∷ Toff013 ∷ CCZ023 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ [])
  b7 = at 2 2 [] wn00003 ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b8 : Chain (Toff013 ∷ Toff013 ∷ CCZ023 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (Toff013 ∷ Toff013 ∷ CCZ023 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ [])
  b8 = at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 10 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 11 2 [] wn00003 ▸ done

  b9 : Chain (Toff013 ∷ Toff013 ∷ CCZ023 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (Toff013 ∷ Toff013 ∷ CCZ023 ∷ K0 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ [])
  b9 = at 10 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 9 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00003 ▸
       at 7 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00003 ▸
       at 5 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸ done

  b10 : Chain (Toff013 ∷ Toff013 ∷ CCZ023 ∷ K0 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (Toff013 ∷ Toff013 ∷ CS23 ∷ Sw01 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ [])
  b10 = at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸
       at 3 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 4 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) wn00056 ▸
       at 4 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸ done

  b11 : Chain (Toff013 ∷ Toff013 ∷ CS23 ∷ Sw01 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (Toff013 ∷ Toff013 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ Sw01 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ [])
  b11 = at 3 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 4 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 5 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b12 : Chain (Toff013 ∷ Toff013 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ Sw01 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (Toff013 ∷ Toff013 ∷ CS23 ∷ Sw23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ Toff012 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ [])
  b12 = at 7 2 [] wn00031 ▸
       at 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00003 ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw23 ∷ CS23⁻ ∷ []) wn01882 ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸ done

  b13 : Chain (Toff013 ∷ Toff013 ∷ CS23 ∷ Sw23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ Toff012 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (Toff013 ∷ Toff013 ∷ Sw23 ∷ Sw01 ∷ CS23 ∷ CX13 ∷ Sw01 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ Toff012 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ [])
  b13 = at 2 2 (Sw23 ∷ CS23 ∷ []) wn01883 ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 4 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 6 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸ done

  b14 : Chain (Toff013 ∷ Toff013 ∷ Sw23 ∷ Sw01 ∷ CS23 ∷ CX13 ∷ Sw01 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ Toff012 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (Toff013 ∷ Toff013 ∷ Sw23 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Toff012 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ [])
  b14 = at 6 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 8 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 4 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00073 ▸ done

  b15 : Chain (Toff013 ∷ Toff013 ∷ Sw23 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Toff012 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (Toff013 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ CCZ023 ∷ Toff012 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ [])
  b15 = at 4 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b16 : Chain (Toff013 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ CCZ023 ∷ Toff012 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (Toff013 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ CCZ023 ∷ Toff012 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ [])
  b16 = at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 9 2 [] wn00003 ▸ done

  b17 : Chain (Toff013 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ CCZ023 ∷ Toff012 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (Toff013 ∷ K0 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ CCZ023 ∷ Toff012 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ [])
  b17 = at 8 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 7 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00003 ▸
       at 5 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸
       at 3 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸ done

  b18 : Chain (Toff013 ∷ K0 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ CCZ023 ∷ Toff012 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (Toff013 ∷ Sw23 ∷ Toff012 ∷ CCZ023 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ Sw12 ∷ ι ∷ Sw12 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ [])
  b18 = at 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸
       at 1 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 2 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) wn00056 ▸
       at 2 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 5 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (Sw12 ∷ ι ∷ []) (low₁-comm (iI) (Swap)) ▸ done

  b19 : Chain (Toff013 ∷ Sw23 ∷ Toff012 ∷ CCZ023 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ Sw12 ∷ ι ∷ Sw12 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (Toff013 ∷ Sw23 ∷ Toff012 ∷ CCZ023 ∷ K0 ∷ CS12 ∷ Sw12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ [])
  b19 = at 10 2 (Sw12 ∷ K0 ∷ []) (low₁-comm (K) (Swap)) ▸
       at 9 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] wn00014 ▸
       at 8 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 9 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw12 ∷ CS12⁻ ∷ []) wn00015 ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 7 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸ done

  b20 : Chain (Toff013 ∷ Sw23 ∷ Toff012 ∷ CCZ023 ∷ K0 ∷ CS12 ∷ Sw12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (Toff013 ∷ Sw23 ∷ Toff012 ∷ CS23 ∷ CX02 ∷ Sw01 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw12 ∷ Toff012 ∷ Sw12 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ [])
  b20 = at 5 2 (Sw12 ∷ CS12 ∷ []) wn00016 ▸
       at 4 2 (Sw12 ∷ K0 ∷ []) (low₁-comm (K) (Swap)) ▸
       at 5 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) wn00046 ▸
       at 5 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 4 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸ done

  b21 : Chain (Toff013 ∷ Sw23 ∷ Toff012 ∷ CS23 ∷ CX02 ∷ Sw01 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw12 ∷ Toff012 ∷ Sw12 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (Toff013 ∷ Sw23 ∷ Toff012 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw12 ∷ Toff012 ∷ Sw12 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ [])
  b21 = at 5 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 6 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00031 ▸ done

  b22 : Chain (Toff013 ∷ Sw23 ∷ Toff012 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw12 ∷ Toff012 ∷ Sw12 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (Toff013 ∷ Sw23 ∷ Toff012 ∷ CS23 ∷ CX02 ∷ Sw12 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Toff012 ∷ Sw12 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ [])
  b22 = at 7 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) wn00022 ▸
       at 9 2 (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap)) ▸
       at 7 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) wn00023 ▸
       at 8 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00014 ▸
       at 5 2 (Sw12 ∷ CS13⁻ ∷ []) wn00047 ▸ done

  b23 : Chain (Toff013 ∷ Sw23 ∷ Toff012 ∷ CS23 ∷ CX02 ∷ Sw12 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Toff012 ∷ Sw12 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (Toff013 ∷ Sw23 ∷ Toff012 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ Sw23 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ Toff012 ∷ Sw12 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ [])
  b23 = at 4 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00014 ▸
       at 3 2 (Sw12 ∷ CS13 ∷ []) wn00048 ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b24 : Chain (Toff013 ∷ Sw23 ∷ Toff012 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ Sw23 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ Toff012 ∷ Sw12 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (Toff013 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw12 ∷ CCZ013 ∷ Toff012 ∷ Sw12 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ [])
  b24 = at 7 2 [] wn00003 ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00003 ▸
       at 5 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00043 ▸
       at 5 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 4 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸ done

  b25 : Chain (Toff013 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw12 ∷ CCZ013 ∷ Toff012 ∷ Sw12 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (Toff013 ∷ Sw23 ∷ K0 ∷ CS12 ∷ Sw12 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K0 ∷ ι ∷ CCZ013 ∷ Toff012 ∷ Sw12 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ [])
  b25 = at 9 2 (Sw12 ∷ ι ∷ []) (low₁-comm (iI) (Swap)) ▸
       at 8 2 (Sw12 ∷ K0 ∷ []) (low₁-comm (K) (Swap)) ▸
       at 7 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00014 ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 7 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw12 ∷ CS12⁻ ∷ []) wn00015 ▸
       at 4 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸ done

  b26 : Chain (Toff013 ∷ Sw23 ∷ K0 ∷ CS12 ∷ Sw12 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K0 ∷ ι ∷ CCZ013 ∷ Toff012 ∷ Sw12 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (Toff013 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ CCZ123 ∷ Sw12 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ [])
  b26 = at 5 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw12 ∷ CS12 ∷ []) wn00016 ▸
       at 2 2 (Sw12 ∷ K0 ∷ []) (low₁-comm (K) (Swap)) ▸
       at 3 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) wn00046 ▸
       at 3 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (CCZ013 ∷ CCZ123 ∷ []) (ax toff-ccz) ▸
       at 3 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸ done

  b27 : Chain (Toff013 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ CCZ123 ∷ Sw12 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (Toff013 ∷ Sw23 ∷ Sw12 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ CCZ123 ∷ Sw12 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ [])
  b27 = at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b28 : Chain (Toff013 ∷ Sw23 ∷ Sw12 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ CCZ123 ∷ Sw12 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (Toff013 ∷ Sw23 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ CCZ123 ∷ Sw12 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ [])
  b28 = at 8 2 [] wn00003 ▸
       at 2 2 (CS23 ∷ Sw12 ∷ []) wn00020 ▸
       at 5 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 3 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS23⁻ ∷ Sw12 ∷ []) wn00021 ▸
       at 7 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 5 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b29 : Chain (Toff013 ∷ Sw23 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ CCZ123 ∷ Sw12 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (Toff013 ∷ Sw23 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ Sw01 ∷ CX02 ∷ CS03 ∷ Sw12 ∷ CCZ123 ∷ Sw12 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ [])
  b29 = at 6 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) wn00022 ▸
       at 8 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 9 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) wn00023 ▸
       at 6 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 3 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 4 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 5 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸ done

  b30 : Chain (Toff013 ∷ Sw23 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ Sw01 ∷ CX02 ∷ CS03 ∷ Sw12 ∷ CCZ123 ∷ Sw12 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (Toff013 ∷ Sw23 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ CCZ123 ∷ Sw12 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ [])
  b30 = at 6 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸
       at 3 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸ done

  b31 : Chain (Toff013 ∷ Sw23 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ CCZ123 ∷ Sw12 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (Toff013 ∷ Sw23 ∷ CCZ023 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ [])
  b31 = at 2 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS13 ∷ Sw12 ∷ []) wn00049 ▸
       at 4 2 (CX21 ∷ Sw12 ∷ []) wn00050 ▸
       at 5 2 (CS13⁻ ∷ Sw12 ∷ []) wn00051 ▸
       at 6 2 (CX21 ∷ Sw12 ∷ []) wn00050 ▸
       at 7 2 (CS23 ∷ Sw12 ∷ []) wn00020 ▸
       at 3 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00052 ▸ done

  b32 : Chain (Toff013 ∷ Sw23 ∷ CCZ023 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (Toff013 ∷ Sw23 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ Sw01 ∷ CCZ123 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ [])
  b32 = at 3 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00014 ▸
       at 2 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 3 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 4 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 5 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸ done

  b33 : Chain (Toff013 ∷ Sw23 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ Sw01 ∷ CCZ123 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS23 ∷ Sw23 ∷ CX02 ∷ Sw23 ∷ Sw23 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ CCZ123 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ [])
  b33 = at 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00031 ▸
       at 1 2 (CS23 ∷ Sw23 ∷ []) wn00071 ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b34 : Chain (Toff013 ∷ CS23 ∷ Sw23 ∷ CX02 ∷ Sw23 ∷ Sw23 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ CCZ123 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (Toff013 ∷ Sw01 ∷ CS23 ∷ Sw01 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ Sw23 ∷ CCZ123 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ [])
  b34 = at 2 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS23⁻ ∷ Sw23 ∷ []) wn00072 ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 1 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 2 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸ done

  b35 : Chain (Toff013 ∷ Sw01 ∷ CS23 ∷ Sw01 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ Sw23 ∷ CCZ123 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (Toff013 ∷ Sw01 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ Sw23 ∷ Sw01 ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ CCZ123 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ [])
  b35 = at 4 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 4 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 3 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 6 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b36 : Chain (Toff013 ∷ Sw01 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ Sw23 ∷ Sw01 ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ CCZ123 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (Toff013 ∷ CCZ023 ∷ Sw23 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ [])
  b36 = at 6 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 2 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00073 ▸
       at 2 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b37 : Chain (Toff013 ∷ CCZ023 ∷ Sw23 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (Toff013 ∷ CCZ023 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ [])
  b37 = at 2 2 (CS23 ∷ Sw23 ∷ []) wn00071 ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS23⁻ ∷ Sw23 ∷ []) wn00072 ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸ done

  b38 : Chain (Toff013 ∷ CCZ023 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS02 ∷ Sw23 ∷ Toff012 ∷ Toff012 ∷ Sw23 ∷ CCZ023 ∷ Toff013 ∷ CCZ123 ∷ CS02⁻ ∷ [])
  b38 = at 2 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00073 ▸
       at 2 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸
       at 2 2 (CS02 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-CS02) ▸
       at 1 2 (CS02 ∷ CCZ023 ∷ []) (lem-pass-CCZ023-vs-CS02) ▸
       at 3 2 (Toff013 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-TOFF013) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 0 (Toff012 ∷ Toff012 ∷ []) wn00045 ▸ done

  b39 : Chain (Toff013 ∷ CS02 ∷ Sw23 ∷ Toff012 ∷ Toff012 ∷ Sw23 ∷ CCZ023 ∷ Toff013 ∷ CCZ123 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS02 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ K0 ∷ ι ∷ Toff012 ∷ Sw23 ∷ CCZ023 ∷ Toff013 ∷ CCZ123 ∷ CS02⁻ ∷ [])
  b39 = at 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b40 : Chain (Toff013 ∷ CS02 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ K0 ∷ ι ∷ Toff012 ∷ Sw23 ∷ CCZ023 ∷ Toff013 ∷ CCZ123 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS02 ∷ Sw23 ∷ K0 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ CCZ023 ∷ Toff013 ∷ CCZ123 ∷ CS02⁻ ∷ [])
  b40 = at 9 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸ done

  b41 : Chain (Toff013 ∷ CS02 ∷ Sw23 ∷ K0 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ CCZ023 ∷ Toff013 ∷ CCZ123 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS02 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ CCZ023 ∷ Toff013 ∷ CCZ123 ∷ CS02⁻ ∷ [])
  b41 = at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00003 ▸
       at 9 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 10 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸ done

  b42 : Chain (Toff013 ∷ CS02 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ CCZ023 ∷ Toff013 ∷ CCZ123 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ CCZ023 ∷ Toff013 ∷ CCZ123 ∷ CS02⁻ ∷ [])
  b42 = at 3 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) wn00056 ▸
       at 3 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b43 : Chain (Toff013 ∷ CS02 ∷ Toff013 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ CCZ023 ∷ Toff013 ∷ CCZ123 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ CCZ023 ∷ Toff013 ∷ CCZ123 ∷ CS02⁻ ∷ [])
  b43 = at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 10 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b44 : Chain (Toff013 ∷ CS02 ∷ Toff013 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ CCZ023 ∷ Toff013 ∷ CCZ123 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ CCZ023 ∷ Toff013 ∷ CCZ123 ∷ CS02⁻ ∷ [])
  b44 = at 4 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00003 ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b45 : Chain (Toff013 ∷ CS02 ∷ Toff013 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ CCZ023 ∷ Toff013 ∷ CCZ123 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ Toff013 ∷ CCZ023 ∷ Toff013 ∷ Sw23 ∷ Sw23 ∷ CCZ123 ∷ CS02⁻ ∷ [])
  b45 = at 9 2 [] wn00003 ▸
       at 10 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 11 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 4 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) wn00056 ▸
       at 4 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b46 : Chain (Toff013 ∷ CS02 ∷ Toff013 ∷ Toff013 ∷ CCZ023 ∷ Toff013 ∷ Sw23 ∷ Sw23 ∷ CCZ123 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ Toff013 ∷ CCZ023 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CCZ123 ∷ CS02⁻ ∷ [])
  b46 = at 5 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 8 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b47 : Chain (Toff013 ∷ CS02 ∷ Toff013 ∷ Toff013 ∷ CCZ023 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CCZ123 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ Toff013 ∷ CCZ023 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw23 ∷ CCZ123 ∷ CS02⁻ ∷ [])
  b47 = at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 10 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 12 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 13 2 [] wn00003 ▸
       at 12 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 11 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸ done

  b48 : Chain (Toff013 ∷ CS02 ∷ Toff013 ∷ Toff013 ∷ CCZ023 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw23 ∷ CCZ123 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ Toff013 ∷ CCZ023 ∷ K0 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ CCZ123 ∷ CS02⁻ ∷ [])
  b48 = at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] wn00003 ▸
       at 9 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00003 ▸
       at 7 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00003 ▸ done

  b49 : Chain (Toff013 ∷ CS02 ∷ Toff013 ∷ Toff013 ∷ CCZ023 ∷ K0 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ CCZ123 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ Toff013 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ CCZ123 ∷ CS02⁻ ∷ [])
  b49 = at 5 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 6 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) wn00056 ▸
       at 6 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 5 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 6 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸ done

  b50 : Chain (Toff013 ∷ CS02 ∷ Toff013 ∷ Toff013 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ CCZ123 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ Toff013 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ CCZ123 ∷ CS02⁻ ∷ [])
  b50 = at 7 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00031 ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b51 : Chain (Toff013 ∷ CS02 ∷ Toff013 ∷ Toff013 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ CCZ123 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ Toff013 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ Toff012 ∷ Sw23 ∷ CCZ123 ∷ CS02⁻ ∷ [])
  b51 = at 10 2 [] wn00003 ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 8 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw23 ∷ CS23⁻ ∷ []) wn01882 ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw23 ∷ CS23 ∷ []) wn01883 ▸
       at 5 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸ done

  b52 : Chain (Toff013 ∷ CS02 ∷ Toff013 ∷ Toff013 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ Toff012 ∷ Sw23 ∷ CCZ123 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ Toff013 ∷ Sw23 ∷ Sw01 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ Sw01 ∷ Sw23 ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Toff012 ∷ Sw23 ∷ CCZ123 ∷ CS02⁻ ∷ [])
  b52 = at 6 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 8 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 10 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b53 : Chain (Toff013 ∷ CS02 ∷ Toff013 ∷ Toff013 ∷ Sw23 ∷ Sw01 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ Sw01 ∷ Sw23 ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Toff012 ∷ Sw23 ∷ CCZ123 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ Toff013 ∷ Sw23 ∷ CCZ023 ∷ Toff012 ∷ Sw23 ∷ CCZ123 ∷ CS02⁻ ∷ [])
  b53 = at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 6 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00073 ▸
       at 6 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸ done

  b54 : Chain (Toff013 ∷ CS02 ∷ Toff013 ∷ Toff013 ∷ Sw23 ∷ CCZ023 ∷ Toff012 ∷ Sw23 ∷ CCZ123 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ CCZ023 ∷ Toff012 ∷ Sw23 ∷ CCZ123 ∷ CS02⁻ ∷ [])
  b54 = at 3 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b55 : Chain (Toff013 ∷ CS02 ∷ Toff013 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ CCZ023 ∷ Toff012 ∷ Sw23 ∷ CCZ123 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ K0 ∷ ι ∷ CCZ023 ∷ Toff012 ∷ Sw23 ∷ CCZ123 ∷ CS02⁻ ∷ [])
  b55 = at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 10 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 11 2 [] wn00003 ▸
       at 10 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 9 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸ done

  b56 : Chain (Toff013 ∷ CS02 ∷ Toff013 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ K0 ∷ ι ∷ CCZ023 ∷ Toff012 ∷ Sw23 ∷ CCZ123 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ K0 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ CCZ023 ∷ Toff012 ∷ Sw23 ∷ CCZ123 ∷ CS02⁻ ∷ [])
  b56 = at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00003 ▸
       at 7 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00003 ▸
       at 5 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸ done

  b57 : Chain (Toff013 ∷ CS02 ∷ Toff013 ∷ K0 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ CCZ023 ∷ Toff012 ∷ Sw23 ∷ CCZ123 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ Sw23 ∷ Toff012 ∷ CCZ023 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw12 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ CCZ123 ∷ CS02⁻ ∷ [])
  b57 = at 3 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 4 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) wn00056 ▸
       at 4 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 6 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (Sw12 ∷ ι ∷ []) (low₁-comm (iI) (Swap)) ▸
       at 12 2 (Sw12 ∷ K0 ∷ []) (low₁-comm (K) (Swap)) ▸
       at 11 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸ done

  b58 : Chain (Toff013 ∷ CS02 ∷ Toff013 ∷ Sw23 ∷ Toff012 ∷ CCZ023 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw12 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ CCZ123 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ Sw23 ∷ Toff012 ∷ CCZ023 ∷ Sw12 ∷ K0 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ CCZ123 ∷ CS02⁻ ∷ [])
  b58 = at 13 2 [] wn00014 ▸
       at 10 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 11 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw12 ∷ CS12⁻ ∷ []) wn00015 ▸
       at 8 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 9 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw12 ∷ CS12 ∷ []) wn00016 ▸
       at 6 2 (Sw12 ∷ K0 ∷ []) (low₁-comm (K) (Swap)) ▸ done

  b59 : Chain (Toff013 ∷ CS02 ∷ Toff013 ∷ Sw23 ∷ Toff012 ∷ CCZ023 ∷ Sw12 ∷ K0 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ CCZ123 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ Sw23 ∷ Toff012 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ Sw01 ∷ Sw12 ∷ Toff012 ∷ Sw12 ∷ Sw23 ∷ CCZ123 ∷ CS02⁻ ∷ [])
  b59 = at 7 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) wn00046 ▸
       at 7 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 6 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 7 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 8 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸ done

  b60 : Chain (Toff013 ∷ CS02 ∷ Toff013 ∷ Sw23 ∷ Toff012 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ Sw01 ∷ Sw12 ∷ Toff012 ∷ Sw12 ∷ Sw23 ∷ CCZ123 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ Sw23 ∷ Toff012 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ Toff012 ∷ Sw12 ∷ Sw23 ∷ CCZ123 ∷ CS02⁻ ∷ [])
  b60 = at 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00031 ▸
       at 9 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) wn00022 ▸ done

  b61 : Chain (Toff013 ∷ CS02 ∷ Toff013 ∷ Sw23 ∷ Toff012 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ Toff012 ∷ Sw12 ∷ Sw23 ∷ CCZ123 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ Sw23 ∷ Toff012 ∷ CS23 ∷ Sw12 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Toff012 ∷ Sw12 ∷ Sw23 ∷ CCZ123 ∷ CS02⁻ ∷ [])
  b61 = at 11 2 (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap)) ▸
       at 9 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) wn00023 ▸
       at 10 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00014 ▸
       at 7 2 (Sw12 ∷ CS13⁻ ∷ []) wn00047 ▸
       at 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00014 ▸ done

  b62 : Chain (Toff013 ∷ CS02 ∷ Toff013 ∷ Sw23 ∷ Toff012 ∷ CS23 ∷ Sw12 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Toff012 ∷ Sw12 ∷ Sw23 ∷ CCZ123 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ Sw23 ∷ Toff012 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ Sw12 ∷ Sw23 ∷ CCZ123 ∷ CS02⁻ ∷ [])
  b62 = at 5 2 (Sw12 ∷ CS13 ∷ []) wn00048 ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00003 ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00003 ▸
       at 10 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b63 : Chain (Toff013 ∷ CS02 ∷ Toff013 ∷ Sw23 ∷ Toff012 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ Sw12 ∷ Sw23 ∷ CCZ123 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw12 ∷ K0 ∷ ι ∷ CCZ013 ∷ Toff012 ∷ Sw12 ∷ Sw23 ∷ CCZ123 ∷ CS02⁻ ∷ [])
  b63 = at 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] wn00003 ▸
       at 7 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00043 ▸
       at 7 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 6 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (Sw12 ∷ ι ∷ []) (low₁-comm (iI) (Swap)) ▸
       at 10 2 (Sw12 ∷ K0 ∷ []) (low₁-comm (K) (Swap)) ▸ done

  b64 : Chain (Toff013 ∷ CS02 ∷ Toff013 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw12 ∷ K0 ∷ ι ∷ CCZ013 ∷ Toff012 ∷ Sw12 ∷ Sw23 ∷ CCZ123 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ Sw23 ∷ K0 ∷ Sw12 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K0 ∷ ι ∷ CCZ013 ∷ Toff012 ∷ Sw12 ∷ Sw23 ∷ CCZ123 ∷ CS02⁻ ∷ [])
  b64 = at 9 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] wn00014 ▸
       at 8 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 9 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw12 ∷ CS12⁻ ∷ []) wn00015 ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 7 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw12 ∷ CS12 ∷ []) wn00016 ▸ done

  b65 : Chain (Toff013 ∷ CS02 ∷ Toff013 ∷ Sw23 ∷ K0 ∷ Sw12 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K0 ∷ ι ∷ CCZ013 ∷ Toff012 ∷ Sw12 ∷ Sw23 ∷ CCZ123 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ Sw23 ∷ Sw12 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ CCZ123 ∷ Sw12 ∷ Sw23 ∷ CCZ123 ∷ CS02⁻ ∷ [])
  b65 = at 4 2 (Sw12 ∷ K0 ∷ []) (low₁-comm (K) (Swap)) ▸
       at 5 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) wn00046 ▸
       at 5 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (CCZ013 ∷ CCZ123 ∷ []) (ax toff-ccz) ▸
       at 5 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b66 : Chain (Toff013 ∷ CS02 ∷ Toff013 ∷ Sw23 ∷ Sw12 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ CCZ123 ∷ Sw12 ∷ Sw23 ∷ CCZ123 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ Sw23 ∷ CS23 ∷ Sw12 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ CCZ123 ∷ Sw12 ∷ Sw23 ∷ CCZ123 ∷ CS02⁻ ∷ [])
  b66 = at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 7 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00003 ▸
       at 4 2 (CS23 ∷ Sw12 ∷ []) wn00020 ▸ done

  b67 : Chain (Toff013 ∷ CS02 ∷ Toff013 ∷ Sw23 ∷ CS23 ∷ Sw12 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ CCZ123 ∷ Sw12 ∷ Sw23 ∷ CCZ123 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ Sw23 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ CCZ123 ∷ Sw12 ∷ Sw23 ∷ CCZ123 ∷ CS02⁻ ∷ [])
  b67 = at 7 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 5 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS23⁻ ∷ Sw12 ∷ []) wn00021 ▸
       at 9 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 7 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 9 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) wn00022 ▸
       at 10 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸ done

  b68 : Chain (Toff013 ∷ CS02 ∷ Toff013 ∷ Sw23 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ CCZ123 ∷ Sw12 ∷ Sw23 ∷ CCZ123 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ Sw23 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw12 ∷ CCZ123 ∷ Sw12 ∷ Sw23 ∷ CCZ123 ∷ CS02⁻ ∷ [])
  b68 = at 11 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) wn00023 ▸
       at 8 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 4 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 5 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 6 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 7 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 8 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b69 : Chain (Toff013 ∷ CS02 ∷ Toff013 ∷ Sw23 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw12 ∷ CCZ123 ∷ Sw12 ∷ Sw23 ∷ CCZ123 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ Sw23 ∷ CCZ023 ∷ Sw12 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw12 ∷ Sw23 ∷ CCZ123 ∷ CS02⁻ ∷ [])
  b69 = at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸
       at 5 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 4 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b70 : Chain (Toff013 ∷ CS02 ∷ Toff013 ∷ Sw23 ∷ CCZ023 ∷ Sw12 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw12 ∷ Sw23 ∷ CCZ123 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ Sw23 ∷ CCZ023 ∷ CCZ123 ∷ Sw23 ∷ CCZ123 ∷ CS02⁻ ∷ [])
  b70 = at 5 2 (CS13 ∷ Sw12 ∷ []) wn00049 ▸
       at 6 2 (CX21 ∷ Sw12 ∷ []) wn00050 ▸
       at 7 2 (CS13⁻ ∷ Sw12 ∷ []) wn00051 ▸
       at 8 2 (CX21 ∷ Sw12 ∷ []) wn00050 ▸
       at 9 2 (CS23 ∷ Sw12 ∷ []) wn00020 ▸
       at 5 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00052 ▸
       at 5 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00014 ▸ done

  b71 : Chain (Toff013 ∷ CS02 ∷ Toff013 ∷ Sw23 ∷ CCZ023 ∷ CCZ123 ∷ Sw23 ∷ CCZ123 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ Sw23 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ CCZ123 ∷ Sw23 ∷ CCZ123 ∷ CS02⁻ ∷ [])
  b71 = at 4 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 5 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 6 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 7 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b72 : Chain (Toff013 ∷ CS02 ∷ Toff013 ∷ Sw23 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ CCZ123 ∷ Sw23 ∷ CCZ123 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ Sw23 ∷ CX02 ∷ CS03 ∷ CCZ123 ∷ Sw23 ∷ CCZ123 ∷ CS02⁻ ∷ [])
  b72 = at 9 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00031 ▸
       at 3 2 (CS23 ∷ Sw23 ∷ []) wn00071 ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS23⁻ ∷ Sw23 ∷ []) wn00072 ▸ done

  b73 : Chain (Toff013 ∷ CS02 ∷ Toff013 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ Sw23 ∷ CX02 ∷ CS03 ∷ CCZ123 ∷ Sw23 ∷ CCZ123 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ Sw01 ∷ CS23 ∷ Sw23 ∷ Sw01 ∷ CX02 ∷ Sw23 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ Sw23 ∷ CCZ123 ∷ Sw23 ∷ CCZ123 ∷ CS02⁻ ∷ [])
  b73 = at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00003 ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 4 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 6 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b74 : Chain (Toff013 ∷ CS02 ∷ Toff013 ∷ Sw01 ∷ CS23 ∷ Sw23 ∷ Sw01 ∷ CX02 ∷ Sw23 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ Sw23 ∷ CCZ123 ∷ Sw23 ∷ CCZ123 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ Sw01 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ Sw01 ∷ CS02 ∷ Sw23 ∷ CCZ123 ∷ Sw23 ∷ CCZ123 ∷ CS02⁻ ∷ [])
  b74 = at 6 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 8 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b75 : Chain (Toff013 ∷ CS02 ∷ Toff013 ∷ Sw01 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ Sw01 ∷ CS02 ∷ Sw23 ∷ CCZ123 ∷ Sw23 ∷ CCZ123 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ CCZ023 ∷ CS23 ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ Sw23 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw23 ∷ CCZ123 ∷ CS02⁻ ∷ [])
  b75 = at 7 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 4 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00073 ▸
       at 4 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS23 ∷ Sw23 ∷ []) wn00071 ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b76 : Chain (Toff013 ∷ CS02 ∷ Toff013 ∷ CCZ023 ∷ CS23 ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ Sw23 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw23 ∷ CCZ123 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ CCZ023 ∷ CCZ123 ∷ Sw23 ∷ Sw23 ∷ CCZ123 ∷ CS02⁻ ∷ [])
  b76 = at 5 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS23⁻ ∷ Sw23 ∷ []) wn00072 ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 7 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00003 ▸
       at 4 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00073 ▸
       at 4 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸ done

  b77 : Chain (Toff013 ∷ CS02 ∷ Toff013 ∷ CCZ023 ∷ CCZ123 ∷ Sw23 ∷ Sw23 ∷ CCZ123 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ CCZ023 ∷ [])
  b77 = at 5 2 [] wn00003 ▸
       at 4 2 [] wn00033 ▸
       at 3 2 (CS02⁻ ∷ CCZ023 ∷ []) (lem-pass-CCZ023-vs-CSd02) ▸ done

-- pass [CZ23 CCZ123] [TOFF012 CS03 TOFF012 CSd03]: 8 steps
lem-pass-CZ23-CCZ123-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (CZ23 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CZ23 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CZ23-CCZ123-vs-TOFF012-CS03-TOFF012-CSd03 = run b0
  where
  b0 : Chain (CZ23 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CZ23 ∷ CCZ123 ∷ [])
  b0 = at 1 2 (Toff012 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-TOFF012) ▸
       at 0 2 (Toff012 ∷ CZ23 ∷ []) (sym lem-pass-TOFF012-vs-CZ23) ▸
       at 2 2 (CS03 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-CS03) ▸
       at 1 2 (CS03 ∷ CZ23 ∷ []) (sym lem-pass-CS03-vs-CZ23) ▸
       at 3 2 (Toff012 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-TOFF012) ▸
       at 2 2 (Toff012 ∷ CZ23 ∷ []) (sym lem-pass-TOFF012-vs-CZ23) ▸
       at 4 2 (CS03⁻ ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-CSd03) ▸
       at 3 2 (CS03⁻ ∷ CZ23 ∷ []) (sym lem-pass-CSd03-vs-CZ23) ▸ done

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D679 where

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
open import Examples.Groups.Clifford+CS.Four.Wins.W01 using (wn00001 ; wn00003 ; wn00005 ; wn00007 ; wn00008 ; wn00009 ; wn00010 ; wn00012 ; wn00014 ; wn00015 ; wn00016 ; wn00018 ; wn00019 ; wn00020 ; wn00021 ; wn00022 ; wn00023 ; wn00024 ; wn00025 ; wn00027 ; wn00028 ; wn00029 ; wn00030 ; wn00031 ; wn00047 ; wn00048 ; wn00071 ; wn00072 ; wn00122 ; wn00123 ; wn00124 ; wn00127)
open import Examples.Groups.Clifford+CS.Four.Wins.W02 using (wn00271 ; wn00272 ; wn00274 ; wn00322 ; wn00333 ; wn00334 ; wn00335 ; wn00340 ; wn00366 ; wn00368 ; wn00385 ; wn00398)
open import Examples.Groups.Clifford+CS.Four.Wins.W25 using (wn01294)
open import Examples.Groups.Clifford+CS.Four.Wins.W38 using (wn01882 ; wn01883)
open import Examples.Groups.Clifford+CS.Four.D.D651 using (lem-S2)

-- S2 @2103: 343 steps
lem-S2-at2103 : ⟪ (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CS02 ∷ Toff213 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-S2-at2103 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (trans (run b38) (trans (run b39) (trans (run b40) (trans (run b41) (run b42))))))))))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ K2 ∷ CS12 ∷ CX01 ∷ Sw01 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K2 ∷ ι1 ∷ CS23⁻ ∷ Sw01 ∷ [])
  b0 = at 4 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 3 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 2 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw01 ∷ ι1 ∷ []) wn00127 ▸
       at 8 2 (Sw01 ∷ K2 ∷ []) (sym (low-comm (Swap) (K))) ▸
       at 7 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 6 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 5 2 (Sw01 ∷ CS02⁻ ∷ []) wn00009 ▸ done

  b1 : Chain (Toff201 ∷ CS23 ∷ K2 ∷ CS12 ∷ CX01 ∷ Sw01 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K2 ∷ ι1 ∷ CS23⁻ ∷ Sw01 ∷ []) (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ Sw01 ∷ ι1 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Sw01 ∷ [])
  b1 = at 4 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 3 2 (Sw01 ∷ CS02 ∷ []) wn00010 ▸
       at 2 2 (Sw01 ∷ K2 ∷ []) (sym (low-comm (Swap) (K))) ▸
       at 3 8 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) wn00333 ▸
       at 3 8 (Toff201 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 0 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw01 ∷ ι1 ∷ []) wn00127 ▸ done

  b2 : Chain (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ Sw01 ∷ ι1 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Sw01 ∷ []) (Sw01 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Sw01 ∷ [])
  b2 = at 6 2 (Sw01 ∷ K2 ∷ []) (sym (low-comm (Swap) (K))) ▸
       at 5 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 4 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 3 2 (Sw01 ∷ CS02⁻ ∷ []) wn00009 ▸
       at 2 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 1 2 (Sw01 ∷ CS02 ∷ []) wn00010 ▸
       at 0 2 (Sw01 ∷ K2 ∷ []) (sym (low-comm (Swap) (K))) ▸
       at 1 8 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) wn00333 ▸ done

  b3 : Chain (Sw01 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Sw01 ∷ []) (Sw01 ∷ Toff201 ∷ CS23 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw12 ∷ CS01 ∷ K1 ∷ ι ∷ CS13⁻ ∷ Sw12 ∷ Sw01 ∷ [])
  b3 = at 1 8 (Toff201 ∷ []) (by-assoc Eq.refl) ▸
       at 5 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 4 2 (Sw12 ∷ CS13⁻ ∷ []) wn00047 ▸
       at 3 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw12 ∷ ι ∷ []) (low₁-comm (iI) (Swap)) ▸
       at 9 2 (Sw12 ∷ K1 ∷ []) wn00398 ▸
       at 8 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00014 ▸ done

  b4 : Chain (Sw01 ∷ Toff201 ∷ CS23 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw12 ∷ CS01 ∷ K1 ∷ ι ∷ CS13⁻ ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Toff201 ∷ CS23 ∷ Sw12 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ CS13⁻ ∷ Sw12 ∷ Sw01 ∷ [])
  b4 = at 7 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 8 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw12 ∷ CS12⁻ ∷ []) wn00015 ▸
       at 5 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 6 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw12 ∷ CS12 ∷ []) wn00016 ▸
       at 3 2 (Sw12 ∷ K1 ∷ []) wn00398 ▸
       at 4 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) wn00366 ▸ done

  b5 : Chain (Sw01 ∷ Toff201 ∷ CS23 ∷ Sw12 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ CS13⁻ ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw12 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ CS01 ∷ K1 ∷ ι ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Sw12 ∷ Sw01 ∷ [])
  b5 = at 4 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw12 ∷ CS13 ∷ []) wn00048 ▸
       at 1 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw12 ∷ ι ∷ []) (low₁-comm (iI) (Swap)) ▸
       at 7 2 (Sw12 ∷ K1 ∷ []) wn00398 ▸
       at 6 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00014 ▸
       at 5 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸ done

  b6 : Chain (Sw01 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw12 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ CS01 ∷ K1 ∷ ι ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Sw12 ∷ Sw01 ∷ [])
  b6 = at 6 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw12 ∷ CS12⁻ ∷ []) wn00015 ▸
       at 3 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw12 ∷ CS12 ∷ []) wn00016 ▸
       at 1 2 (Sw12 ∷ K1 ∷ []) wn00398 ▸
       at 2 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) wn00366 ▸
       at 2 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸ done

  b7 : Chain (Sw01 ∷ Sw12 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ Toff102 ∷ CS13 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ Sw01 ∷ ι1 ∷ CS03⁻ ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b7 = at 6 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 6 2 (Sw01 ∷ CS02⁻ ∷ []) wn00009 ▸
       at 5 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 6 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (Sw01 ∷ ι1 ∷ []) wn00127 ▸ done

  b8 : Chain (Sw01 ∷ Sw12 ∷ Toff102 ∷ CS13 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ Sw01 ∷ ι1 ∷ CS03⁻ ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ Toff102 ∷ CS13 ∷ Sw01 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ CS03⁻ ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b8 = at 10 2 (Sw01 ∷ K0 ∷ []) wn00271 ▸
       at 9 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 8 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 7 2 (Sw01 ∷ CS02⁻ ∷ []) wn00009 ▸
       at 6 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 5 2 (Sw01 ∷ CS02 ∷ []) wn00010 ▸
       at 4 2 (Sw01 ∷ K0 ∷ []) wn00271 ▸
       at 5 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) wn00272 ▸ done

  b9 : Chain (Sw01 ∷ Sw12 ∷ Toff102 ∷ CS13 ∷ Sw01 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ CS03⁻ ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ Sw01 ∷ ι1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b9 = at 5 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 4 2 (Sw01 ∷ CS02 ∷ []) wn00010 ▸
       at 3 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 4 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw01 ∷ ι1 ∷ []) wn00127 ▸ done

  b10 : Chain (Sw01 ∷ Sw12 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ Sw01 ∷ ι1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ Sw01 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b10 = at 8 2 (Sw01 ∷ K0 ∷ []) wn00271 ▸
       at 7 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 6 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 5 2 (Sw01 ∷ CS02⁻ ∷ []) wn00009 ▸
       at 4 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 3 2 (Sw01 ∷ CS02 ∷ []) wn00010 ▸
       at 2 2 (Sw01 ∷ K0 ∷ []) wn00271 ▸
       at 3 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) wn00272 ▸ done

  b11 : Chain (Sw01 ∷ Sw12 ∷ Sw01 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ Sw01 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b11 = at 3 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 3 4 (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (lem-S2) ▸
       at 3 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b12 : Chain (Sw01 ∷ Sw12 ∷ Sw01 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ Sw01 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b12 = at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 10 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 11 2 [] wn00003 ▸ done

  b13 : Chain (Sw01 ∷ Sw12 ∷ Sw01 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ K1 ∷ CS03 ∷ CX10 ∷ Sw01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b13 = at 2 2 (K1 ∷ Sw01 ∷ []) wn00123 ▸
       at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 4 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 3 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX10 ∷ Sw01 ∷ []) wn00028 ▸
       at 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b14 : Chain (Sw01 ∷ Sw12 ∷ K1 ∷ CS03 ∷ CX10 ∷ Sw01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ K1 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ Sw23 ∷ CS12 ∷ Sw01 ∷ Sw23 ∷ K0 ∷ ι ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b14 = at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX10 ∷ Sw01 ∷ []) wn00028 ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸ done

  b15 : Chain (Sw01 ∷ Sw12 ∷ K1 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ Sw23 ∷ CS12 ∷ Sw01 ∷ Sw23 ∷ K0 ∷ ι ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ Sw23 ∷ K1 ∷ CS02 ∷ Sw23 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b15 = at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K1 ∷ Sw01 ∷ []) wn00123 ▸
       at 9 2 (ι1 ∷ Sw01 ∷ []) wn00124 ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸ done

  b16 : Chain (Sw01 ∷ Sw12 ∷ Sw23 ∷ K1 ∷ CS02 ∷ Sw23 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ Sw23 ∷ K1 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K1 ∷ ι1 ∷ Sw23 ∷ Sw01 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b16 = at 5 2 (CX10 ∷ Sw23 ∷ []) (sym (low-comm (CX₁₀) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸
       at 7 2 (CX10 ∷ Sw23 ∷ []) (sym (low-comm (CX₁₀) (Swap))) ▸
       at 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00003 ▸
       at 9 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 10 2 (ι1 ∷ Sw23 ∷ []) (sym (low-comm ((iI ↑)) (Swap))) ▸ done

  b17 : Chain (Sw01 ∷ Sw12 ∷ Sw23 ∷ K1 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K1 ∷ ι1 ∷ Sw23 ∷ Sw01 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ Toff103 ∷ CS12 ∷ Sw01 ∷ K0 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ CS02⁻ ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b17 = at 3 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) wn00274 ▸
       at 3 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff103 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 5 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b18 : Chain (Sw01 ∷ Sw12 ∷ Toff103 ∷ CS12 ∷ Sw01 ∷ K0 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ CS02⁻ ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ Toff103 ∷ CS12 ∷ Sw01 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ Sw23 ∷ ι ∷ Sw23 ∷ CS02⁻ ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b18 = at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 8 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 10 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸ done

  b19 : Chain (Sw01 ∷ Sw12 ∷ Toff103 ∷ CS12 ∷ Sw01 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ Sw23 ∷ ι ∷ Sw23 ∷ CS02⁻ ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ Toff103 ∷ CS12 ∷ K1 ∷ CS03 ∷ Sw01 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ CS02⁻ ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b19 = at 12 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 13 2 [] wn00003 ▸
       at 4 2 (K1 ∷ Sw01 ∷ []) wn00123 ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b20 : Chain (Sw01 ∷ Sw12 ∷ Toff103 ∷ CS12 ∷ K1 ∷ CS03 ∷ Sw01 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ CS02⁻ ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ Toff103 ∷ CS12 ∷ K1 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ Sw01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ K0 ∷ ι ∷ CS02⁻ ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b20 = at 6 2 (CX10 ∷ Sw01 ∷ []) wn00028 ▸
       at 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX10 ∷ Sw01 ∷ []) wn00028 ▸
       at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b21 : Chain (Sw01 ∷ Sw12 ∷ Toff103 ∷ CS12 ∷ K1 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ Sw01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ K0 ∷ ι ∷ CS02⁻ ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ Toff103 ∷ CS12 ∷ Sw23 ∷ K1 ∷ Sw23 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ CS02⁻ ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b21 = at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (K1 ∷ Sw01 ∷ []) wn00123 ▸
       at 11 2 (ι1 ∷ Sw01 ∷ []) wn00124 ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸ done

  b22 : Chain (Sw01 ∷ Sw12 ∷ Toff103 ∷ CS12 ∷ Sw23 ∷ K1 ∷ Sw23 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ CS02⁻ ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ Toff103 ∷ CS12 ∷ Sw23 ∷ K1 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Sw23 ∷ K1 ∷ ι1 ∷ Sw01 ∷ CS02⁻ ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b22 = at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸
       at 7 2 (CX10 ∷ Sw23 ∷ []) (sym (low-comm (CX₁₀) (Swap))) ▸
       at 9 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00003 ▸
       at 9 2 (CX10 ∷ Sw23 ∷ []) (sym (low-comm (CX₁₀) (Swap))) ▸
       at 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00003 ▸ done

  b23 : Chain (Sw01 ∷ Sw12 ∷ Toff103 ∷ CS12 ∷ Sw23 ∷ K1 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Sw23 ∷ K1 ∷ ι1 ∷ Sw01 ∷ CS02⁻ ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Sw12 ∷ Sw01 ∷ [])
  b23 = at 11 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 12 2 (ι1 ∷ Sw23 ∷ []) (sym (low-comm ((iI ↑)) (Swap))) ▸
       at 5 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) wn00274 ▸
       at 5 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 4 3 (Toff103 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS12⁻ ∷ Sw01 ∷ []) wn00322 ▸
       at 6 2 [] wn00031 ▸
       at 2 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b24 : Chain (Sw01 ∷ Sw12 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Sw12 ∷ Sw01 ∷ [])
  b24 = at 3 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b25 : Chain (Sw01 ∷ Sw12 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ K2 ∷ CS23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Sw12 ∷ Sw01 ∷ [])
  b25 = at 9 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 10 2 [] wn00003 ▸
       at 1 2 (K2 ∷ Sw12 ∷ []) wn00340 ▸
       at 2 2 (CS23 ∷ Sw12 ∷ []) wn00020 ▸
       at 5 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸ done

  b26 : Chain (Sw01 ∷ K2 ∷ CS23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K1 ∷ ι ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Sw12 ∷ Sw01 ∷ [])
  b26 = at 3 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS23⁻ ∷ Sw12 ∷ []) wn00021 ▸
       at 7 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 5 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) wn00022 ▸
       at 8 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 9 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) wn00023 ▸ done

  b27 : Chain (Sw01 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K1 ∷ ι ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw01 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ Sw01 ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ Sw12 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Sw12 ∷ Sw01 ∷ [])
  b27 = at 6 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K2 ∷ Sw12 ∷ []) wn00340 ▸
       at 8 2 (ι ∷ Sw12 ∷ []) (sym (low₁-comm (iI) (Swap))) ▸
       at 1 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 2 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 3 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 4 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 5 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸ done

  b28 : Chain (Sw01 ∷ Sw01 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ Sw01 ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ Sw12 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw01 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ Sw01 ∷ Sw12 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Sw12 ∷ Sw01 ∷ [])
  b28 = at 6 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 9 2 (ι1 ∷ Sw01 ∷ []) wn00124 ▸ done

  b29 : Chain (Sw01 ∷ Sw01 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ Sw01 ∷ Sw12 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Toff203 ∷ CS12 ∷ Sw12 ∷ K1 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ CS12⁻ ∷ Sw12 ∷ Sw01 ∷ [])
  b29 = at 2 8 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) wn00334 ▸
       at 2 8 (Toff213 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff203 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CS12 ∷ Sw12 ∷ []) wn00018 ▸
       at 4 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b30 : Chain (Sw01 ∷ Toff203 ∷ CS12 ∷ Sw12 ∷ K1 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ CS12⁻ ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Toff203 ∷ CS12 ∷ Sw12 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ Sw23 ∷ ι ∷ Sw23 ∷ CS12⁻ ∷ Sw12 ∷ Sw01 ∷ [])
  b30 = at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 7 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸ done

  b31 : Chain (Sw01 ∷ Toff203 ∷ CS12 ∷ Sw12 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ Sw23 ∷ ι ∷ Sw23 ∷ CS12⁻ ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Toff203 ∷ CS12 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS03 ∷ K1 ∷ ι ∷ CS12⁻ ∷ Sw12 ∷ Sw01 ∷ [])
  b31 = at 11 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 12 2 [] wn00003 ▸
       at 3 2 (K2 ∷ Sw12 ∷ []) wn00340 ▸
       at 4 2 (CS23 ∷ Sw12 ∷ []) wn00020 ▸
       at 7 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 5 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS23⁻ ∷ Sw12 ∷ []) wn00021 ▸
       at 9 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸ done

  b32 : Chain (Sw01 ∷ Toff203 ∷ CS12 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS03 ∷ K1 ∷ ι ∷ CS12⁻ ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Toff203 ∷ CS12 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ Sw12 ∷ CS12⁻ ∷ Sw12 ∷ Sw01 ∷ [])
  b32 = at 7 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 9 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) wn00022 ▸
       at 10 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 11 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) wn00023 ▸
       at 8 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K2 ∷ Sw12 ∷ []) wn00340 ▸
       at 10 2 (ι ∷ Sw12 ∷ []) (sym (low₁-comm (iI) (Swap))) ▸ done

  b33 : Chain (Sw01 ∷ Toff203 ∷ CS12 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ Sw12 ∷ CS12⁻ ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Toff203 ∷ CS12 ∷ Sw01 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ Sw01 ∷ CS02 ∷ Sw23 ∷ K2 ∷ ι ∷ Sw12 ∷ CS12⁻ ∷ Sw12 ∷ Sw01 ∷ [])
  b33 = at 3 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 4 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 5 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 6 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 7 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 8 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b34 : Chain (Sw01 ∷ Toff203 ∷ CS12 ∷ Sw01 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ Sw01 ∷ CS02 ∷ Sw23 ∷ K2 ∷ ι ∷ Sw12 ∷ CS12⁻ ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Toff203 ∷ CS12 ∷ Toff203 ∷ Sw12 ∷ CS12⁻ ∷ Sw12 ∷ Sw01 ∷ [])
  b34 = at 10 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 11 2 (ι1 ∷ Sw01 ∷ []) wn00124 ▸
       at 4 8 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) wn00334 ▸
       at 4 8 (Toff213 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (Toff203 ∷ []) (by-assoc Eq.refl) ▸ done

  b35 : Chain (Sw01 ∷ Toff203 ∷ CS12 ∷ Toff203 ∷ Sw12 ∷ CS12⁻ ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ Sw01 ∷ CS12 ∷ Toff203 ∷ CS12⁻ ∷ Sw01 ∷ [])
  b35 = at 4 2 (CS12⁻ ∷ Sw12 ∷ []) wn00019 ▸
       at 5 2 [] wn00014 ▸
       at 1 1 (Sw01 ∷ Toff213 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 2 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 3 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 4 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸ done

  b36 : Chain (Sw01 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ Sw01 ∷ CS12 ∷ Toff203 ∷ CS12⁻ ∷ Sw01 ∷ []) (Sw01 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ Sw01 ∷ Sw01 ∷ CS12 ∷ Toff203 ∷ CS12⁻ ∷ Sw01 ∷ [])
  b36 = at 5 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 8 2 (ι ∷ Sw01 ∷ []) wn00122 ▸ done

  b37 : Chain (Sw01 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ Sw01 ∷ Sw01 ∷ CS12 ∷ Toff203 ∷ CS12⁻ ∷ Sw01 ∷ []) (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ Sw01 ∷ CS02 ∷ Sw23 ∷ K2 ∷ ι ∷ CS12 ∷ Toff203 ∷ CS12⁻ ∷ Sw01 ∷ [])
  b37 = at 9 2 [] wn00031 ▸
       at 0 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 1 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 2 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 3 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 4 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b38 : Chain (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ Sw01 ∷ CS02 ∷ Sw23 ∷ K2 ∷ ι ∷ CS12 ∷ Toff203 ∷ CS12⁻ ∷ Sw01 ∷ []) (Toff213 ∷ CS02 ∷ Sw01 ∷ Toff203 ∷ CS12⁻ ∷ Sw01 ∷ [])
  b38 = at 6 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 7 2 (ι1 ∷ Sw01 ∷ []) wn00124 ▸
       at 0 8 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) wn00334 ▸
       at 0 8 (Toff213 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸ done

  b39 : Chain (Toff213 ∷ CS02 ∷ Sw01 ∷ Toff203 ∷ CS12⁻ ∷ Sw01 ∷ []) (Toff213 ∷ CS02 ∷ Sw01 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ K2 ∷ ι1 ∷ Sw01 ∷ CS12⁻ ∷ Sw01 ∷ [])
  b39 = at 3 1 (Sw01 ∷ Toff213 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 4 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 5 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 6 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 7 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b40 : Chain (Toff213 ∷ CS02 ∷ Sw01 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ K2 ∷ ι1 ∷ Sw01 ∷ CS12⁻ ∷ Sw01 ∷ []) (Toff213 ∷ CS02 ∷ K2 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ CS12⁻ ∷ Sw01 ∷ [])
  b40 = at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 10 2 (ι ∷ Sw01 ∷ []) wn00122 ▸
       at 11 2 [] wn00031 ▸
       at 2 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸ done

  b41 : Chain (Toff213 ∷ CS02 ∷ K2 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ CS12⁻ ∷ Sw01 ∷ []) (Toff213 ∷ CS02 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ K2 ∷ ι ∷ CS12⁻ ∷ Sw01 ∷ [])
  b41 = at 3 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 4 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 5 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 6 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b42 : Chain (Toff213 ∷ CS02 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ K2 ∷ ι ∷ CS12⁻ ∷ Sw01 ∷ []) (Toff213 ∷ CS02 ∷ Toff213 ∷ CS02⁻ ∷ [])
  b42 = at 7 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 9 2 (ι1 ∷ Sw01 ∷ []) wn00124 ▸
       at 2 8 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) wn00334 ▸
       at 2 8 (Toff213 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸
       at 4 2 [] wn00031 ▸ done

-- S2 @3012: 411 steps
lem-S2-at3012 : ⟪ (Toff301 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-S2-at3012 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (trans (run b38) (trans (run b39) (trans (run b40) (trans (run b41) (trans (run b42) (trans (run b43) (trans (run b44) (trans (run b45) (trans (run b46) (trans (run b47) (trans (run b48) (trans (run b49) (trans (run b50) (run b51)))))))))))))))))))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (Toff301 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ []) (Toff301 ∷ CS23 ∷ K3 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw23 ∷ CS23⁻ ∷ Sw23 ∷ [])
  b0 = at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 2 (Sw23 ∷ CS23⁻ ∷ []) wn01882 ▸
       at 2 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (K3 ∷ Sw23 ∷ []) wn00335 ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b1 : Chain (Toff301 ∷ CS23 ∷ K3 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw23 ∷ CS23⁻ ∷ Sw23 ∷ []) (Toff301 ∷ CS23 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw23 ∷ CS23⁻ ∷ Sw23 ∷ [])
  b1 = at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K3 ∷ Sw23 ∷ []) wn00335 ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 10 2 [] wn00003 ▸ done

  b2 : Chain (Toff301 ∷ CS23 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw23 ∷ CS23⁻ ∷ Sw23 ∷ []) (Toff301 ∷ CS23 ∷ K3 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ CS23⁻ ∷ Sw23 ∷ [])
  b2 = at 9 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 8 2 (Sw23 ∷ K2 ∷ []) wn01294 ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00003 ▸
       at 6 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00003 ▸
       at 4 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸ done

  b3 : Chain (Toff301 ∷ CS23 ∷ K3 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ CS23⁻ ∷ Sw23 ∷ []) (Sw23 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw23 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Sw23 ∷ [])
  b3 = at 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 2 2 (Sw23 ∷ K2 ∷ []) wn01294 ▸
       at 3 8 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) wn00368 ▸
       at 3 8 (Toff201 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw23 ∷ CS23 ∷ []) wn01883 ▸
       at 0 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (Sw23 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw23 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Sw23 ∷ []) (K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw23 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Sw23 ∷ [])
  b4 = at 0 2 (K3 ∷ Sw23 ∷ []) wn00335 ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b5 : Chain (K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw23 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Sw23 ∷ []) (K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ K2 ∷ ι ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Sw23 ∷ [])
  b5 = at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K3 ∷ Sw23 ∷ []) wn00335 ▸
       at 7 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 8 2 [] wn00003 ▸
       at 7 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 6 2 (Sw23 ∷ K2 ∷ []) wn01294 ▸
       at 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00003 ▸ done

  b6 : Chain (K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ K2 ∷ ι ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Sw23 ∷ []) (Sw23 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Sw23 ∷ [])
  b6 = at 4 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 2 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸
       at 0 2 (Sw23 ∷ K2 ∷ []) wn01294 ▸
       at 1 8 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) wn00368 ▸ done

  b7 : Chain (Sw23 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Sw23 ∷ []) (Sw23 ∷ Toff201 ∷ CS23 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw12 ∷ CS01 ∷ K1 ∷ ι ∷ CS13⁻ ∷ Sw12 ∷ Sw23 ∷ [])
  b7 = at 1 8 (Toff201 ∷ []) (by-assoc Eq.refl) ▸
       at 5 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 4 2 (Sw12 ∷ CS13⁻ ∷ []) wn00047 ▸
       at 3 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw12 ∷ ι ∷ []) (low₁-comm (iI) (Swap)) ▸
       at 9 2 (Sw12 ∷ K1 ∷ []) wn00398 ▸
       at 8 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00014 ▸ done

  b8 : Chain (Sw23 ∷ Toff201 ∷ CS23 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw12 ∷ CS01 ∷ K1 ∷ ι ∷ CS13⁻ ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Toff201 ∷ CS23 ∷ Sw12 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ CS13⁻ ∷ Sw12 ∷ Sw23 ∷ [])
  b8 = at 7 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 8 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw12 ∷ CS12⁻ ∷ []) wn00015 ▸
       at 5 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 6 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw12 ∷ CS12 ∷ []) wn00016 ▸
       at 3 2 (Sw12 ∷ K1 ∷ []) wn00398 ▸
       at 4 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) wn00366 ▸ done

  b9 : Chain (Sw23 ∷ Toff201 ∷ CS23 ∷ Sw12 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ CS13⁻ ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw12 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ CS01 ∷ K1 ∷ ι ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Sw12 ∷ Sw23 ∷ [])
  b9 = at 4 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw12 ∷ CS13 ∷ []) wn00048 ▸
       at 1 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw12 ∷ ι ∷ []) (low₁-comm (iI) (Swap)) ▸
       at 7 2 (Sw12 ∷ K1 ∷ []) wn00398 ▸
       at 6 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00014 ▸
       at 5 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸ done

  b10 : Chain (Sw23 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw12 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ CS01 ∷ K1 ∷ ι ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Sw12 ∷ Sw23 ∷ [])
  b10 = at 6 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw12 ∷ CS12⁻ ∷ []) wn00015 ▸
       at 3 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw12 ∷ CS12 ∷ []) wn00016 ▸
       at 1 2 (Sw12 ∷ K1 ∷ []) wn00398 ▸
       at 2 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) wn00366 ▸
       at 2 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸ done

  b11 : Chain (Sw23 ∷ Sw12 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Toff102 ∷ CS13 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ Sw01 ∷ ι1 ∷ CS03⁻ ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b11 = at 6 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 6 2 (Sw01 ∷ CS02⁻ ∷ []) wn00009 ▸
       at 5 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 6 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (Sw01 ∷ ι1 ∷ []) wn00127 ▸ done

  b12 : Chain (Sw23 ∷ Sw12 ∷ Toff102 ∷ CS13 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ Sw01 ∷ ι1 ∷ CS03⁻ ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Toff102 ∷ CS13 ∷ Sw01 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ CS03⁻ ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b12 = at 10 2 (Sw01 ∷ K0 ∷ []) wn00271 ▸
       at 9 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 8 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 7 2 (Sw01 ∷ CS02⁻ ∷ []) wn00009 ▸
       at 6 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 5 2 (Sw01 ∷ CS02 ∷ []) wn00010 ▸
       at 4 2 (Sw01 ∷ K0 ∷ []) wn00271 ▸
       at 5 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) wn00272 ▸ done

  b13 : Chain (Sw23 ∷ Sw12 ∷ Toff102 ∷ CS13 ∷ Sw01 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ CS03⁻ ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ Sw01 ∷ ι1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b13 = at 5 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 4 2 (Sw01 ∷ CS02 ∷ []) wn00010 ▸
       at 3 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 4 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw01 ∷ ι1 ∷ []) wn00127 ▸ done

  b14 : Chain (Sw23 ∷ Sw12 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ Sw01 ∷ ι1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b14 = at 8 2 (Sw01 ∷ K0 ∷ []) wn00271 ▸
       at 7 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 6 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 5 2 (Sw01 ∷ CS02⁻ ∷ []) wn00009 ▸
       at 4 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 3 2 (Sw01 ∷ CS02 ∷ []) wn00010 ▸
       at 2 2 (Sw01 ∷ K0 ∷ []) wn00271 ▸
       at 3 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) wn00272 ▸ done

  b15 : Chain (Sw23 ∷ Sw12 ∷ Sw01 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b15 = at 3 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 3 4 (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (lem-S2) ▸
       at 3 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b16 : Chain (Sw23 ∷ Sw12 ∷ Sw01 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b16 = at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 10 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 11 2 [] wn00003 ▸ done

  b17 : Chain (Sw23 ∷ Sw12 ∷ Sw01 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ K1 ∷ CS03 ∷ CX10 ∷ Sw01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b17 = at 2 2 (K1 ∷ Sw01 ∷ []) wn00123 ▸
       at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 4 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 3 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX10 ∷ Sw01 ∷ []) wn00028 ▸
       at 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b18 : Chain (Sw23 ∷ Sw12 ∷ K1 ∷ CS03 ∷ CX10 ∷ Sw01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ K1 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ Sw23 ∷ CS12 ∷ Sw01 ∷ Sw23 ∷ K0 ∷ ι ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b18 = at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX10 ∷ Sw01 ∷ []) wn00028 ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸ done

  b19 : Chain (Sw23 ∷ Sw12 ∷ K1 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ Sw23 ∷ CS12 ∷ Sw01 ∷ Sw23 ∷ K0 ∷ ι ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ K1 ∷ CS02 ∷ Sw23 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b19 = at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K1 ∷ Sw01 ∷ []) wn00123 ▸
       at 9 2 (ι1 ∷ Sw01 ∷ []) wn00124 ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸ done

  b20 : Chain (Sw23 ∷ Sw12 ∷ Sw23 ∷ K1 ∷ CS02 ∷ Sw23 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ K1 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K1 ∷ ι1 ∷ Sw23 ∷ Sw01 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b20 = at 5 2 (CX10 ∷ Sw23 ∷ []) (sym (low-comm (CX₁₀) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸
       at 7 2 (CX10 ∷ Sw23 ∷ []) (sym (low-comm (CX₁₀) (Swap))) ▸
       at 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00003 ▸
       at 9 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 10 2 (ι1 ∷ Sw23 ∷ []) (sym (low-comm ((iI ↑)) (Swap))) ▸ done

  b21 : Chain (Sw23 ∷ Sw12 ∷ Sw23 ∷ K1 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K1 ∷ ι1 ∷ Sw23 ∷ Sw01 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Toff103 ∷ CS12 ∷ Sw01 ∷ K0 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ CS02⁻ ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b21 = at 3 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) wn00274 ▸
       at 3 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff103 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 5 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b22 : Chain (Sw23 ∷ Sw12 ∷ Toff103 ∷ CS12 ∷ Sw01 ∷ K0 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ CS02⁻ ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Toff103 ∷ CS12 ∷ Sw01 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ Sw23 ∷ ι ∷ Sw23 ∷ CS02⁻ ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b22 = at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 8 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 10 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸ done

  b23 : Chain (Sw23 ∷ Sw12 ∷ Toff103 ∷ CS12 ∷ Sw01 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ Sw23 ∷ ι ∷ Sw23 ∷ CS02⁻ ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Toff103 ∷ CS12 ∷ K1 ∷ CS03 ∷ Sw01 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ CS02⁻ ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b23 = at 12 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 13 2 [] wn00003 ▸
       at 4 2 (K1 ∷ Sw01 ∷ []) wn00123 ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b24 : Chain (Sw23 ∷ Sw12 ∷ Toff103 ∷ CS12 ∷ K1 ∷ CS03 ∷ Sw01 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ CS02⁻ ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Toff103 ∷ CS12 ∷ K1 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ Sw01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ K0 ∷ ι ∷ CS02⁻ ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b24 = at 6 2 (CX10 ∷ Sw01 ∷ []) wn00028 ▸
       at 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX10 ∷ Sw01 ∷ []) wn00028 ▸
       at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b25 : Chain (Sw23 ∷ Sw12 ∷ Toff103 ∷ CS12 ∷ K1 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ Sw01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ K0 ∷ ι ∷ CS02⁻ ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Toff103 ∷ CS12 ∷ Sw23 ∷ K1 ∷ Sw23 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ CS02⁻ ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b25 = at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (K1 ∷ Sw01 ∷ []) wn00123 ▸
       at 11 2 (ι1 ∷ Sw01 ∷ []) wn00124 ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸ done

  b26 : Chain (Sw23 ∷ Sw12 ∷ Toff103 ∷ CS12 ∷ Sw23 ∷ K1 ∷ Sw23 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ CS02⁻ ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Toff103 ∷ CS12 ∷ Sw23 ∷ K1 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Sw23 ∷ K1 ∷ ι1 ∷ Sw01 ∷ CS02⁻ ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b26 = at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸
       at 7 2 (CX10 ∷ Sw23 ∷ []) (sym (low-comm (CX₁₀) (Swap))) ▸
       at 9 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00003 ▸
       at 9 2 (CX10 ∷ Sw23 ∷ []) (sym (low-comm (CX₁₀) (Swap))) ▸
       at 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00003 ▸ done

  b27 : Chain (Sw23 ∷ Sw12 ∷ Toff103 ∷ CS12 ∷ Sw23 ∷ K1 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Sw23 ∷ K1 ∷ ι1 ∷ Sw01 ∷ CS02⁻ ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Sw12 ∷ Sw23 ∷ [])
  b27 = at 11 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 12 2 (ι1 ∷ Sw23 ∷ []) (sym (low-comm ((iI ↑)) (Swap))) ▸
       at 5 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) wn00274 ▸
       at 5 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 4 3 (Toff103 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS12⁻ ∷ Sw01 ∷ []) wn00322 ▸
       at 6 2 [] wn00031 ▸
       at 2 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b28 : Chain (Sw23 ∷ Sw12 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Sw12 ∷ Sw23 ∷ [])
  b28 = at 3 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b29 : Chain (Sw23 ∷ Sw12 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ K2 ∷ CS23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Sw12 ∷ Sw23 ∷ [])
  b29 = at 9 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 10 2 [] wn00003 ▸
       at 1 2 (K2 ∷ Sw12 ∷ []) wn00340 ▸
       at 2 2 (CS23 ∷ Sw12 ∷ []) wn00020 ▸
       at 5 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸ done

  b30 : Chain (Sw23 ∷ K2 ∷ CS23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K1 ∷ ι ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Sw12 ∷ Sw23 ∷ [])
  b30 = at 3 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS23⁻ ∷ Sw12 ∷ []) wn00021 ▸
       at 7 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 5 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) wn00022 ▸
       at 8 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 9 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) wn00023 ▸ done

  b31 : Chain (Sw23 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K1 ∷ ι ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ Sw01 ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ Sw12 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Sw12 ∷ Sw23 ∷ [])
  b31 = at 6 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K2 ∷ Sw12 ∷ []) wn00340 ▸
       at 8 2 (ι ∷ Sw12 ∷ []) (sym (low₁-comm (iI) (Swap))) ▸
       at 1 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 2 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 3 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 4 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 5 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸ done

  b32 : Chain (Sw23 ∷ Sw01 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ Sw01 ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ Sw12 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ Sw01 ∷ Sw12 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Sw12 ∷ Sw23 ∷ [])
  b32 = at 6 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 9 2 (ι1 ∷ Sw01 ∷ []) wn00124 ▸ done

  b33 : Chain (Sw23 ∷ Sw01 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ Sw01 ∷ Sw12 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Toff203 ∷ CS12 ∷ Sw12 ∷ K1 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ CS12⁻ ∷ Sw12 ∷ Sw23 ∷ [])
  b33 = at 2 8 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) wn00334 ▸
       at 2 8 (Toff213 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff203 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CS12 ∷ Sw12 ∷ []) wn00018 ▸
       at 4 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b34 : Chain (Sw23 ∷ Toff203 ∷ CS12 ∷ Sw12 ∷ K1 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ CS12⁻ ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Toff203 ∷ CS12 ∷ Sw12 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ Sw23 ∷ ι ∷ Sw23 ∷ CS12⁻ ∷ Sw12 ∷ Sw23 ∷ [])
  b34 = at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 7 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸ done

  b35 : Chain (Sw23 ∷ Toff203 ∷ CS12 ∷ Sw12 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ Sw23 ∷ ι ∷ Sw23 ∷ CS12⁻ ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Toff203 ∷ CS12 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS03 ∷ K1 ∷ ι ∷ CS12⁻ ∷ Sw12 ∷ Sw23 ∷ [])
  b35 = at 11 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 12 2 [] wn00003 ▸
       at 3 2 (K2 ∷ Sw12 ∷ []) wn00340 ▸
       at 4 2 (CS23 ∷ Sw12 ∷ []) wn00020 ▸
       at 7 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 5 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS23⁻ ∷ Sw12 ∷ []) wn00021 ▸
       at 9 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸ done

  b36 : Chain (Sw23 ∷ Toff203 ∷ CS12 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS03 ∷ K1 ∷ ι ∷ CS12⁻ ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Toff203 ∷ CS12 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ Sw12 ∷ CS12⁻ ∷ Sw12 ∷ Sw23 ∷ [])
  b36 = at 7 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 9 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) wn00022 ▸
       at 10 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 11 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) wn00023 ▸
       at 8 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K2 ∷ Sw12 ∷ []) wn00340 ▸
       at 10 2 (ι ∷ Sw12 ∷ []) (sym (low₁-comm (iI) (Swap))) ▸ done

  b37 : Chain (Sw23 ∷ Toff203 ∷ CS12 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ Sw12 ∷ CS12⁻ ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Toff203 ∷ CS12 ∷ Sw01 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ Sw01 ∷ CS02 ∷ Sw23 ∷ K2 ∷ ι ∷ Sw12 ∷ CS12⁻ ∷ Sw12 ∷ Sw23 ∷ [])
  b37 = at 3 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 4 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 5 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 6 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 7 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 8 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b38 : Chain (Sw23 ∷ Toff203 ∷ CS12 ∷ Sw01 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ Sw01 ∷ CS02 ∷ Sw23 ∷ K2 ∷ ι ∷ Sw12 ∷ CS12⁻ ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Toff203 ∷ CS12 ∷ Toff203 ∷ Sw12 ∷ CS12⁻ ∷ Sw12 ∷ Sw23 ∷ [])
  b38 = at 10 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 11 2 (ι1 ∷ Sw01 ∷ []) wn00124 ▸
       at 4 8 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) wn00334 ▸
       at 4 8 (Toff213 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (Toff203 ∷ []) (by-assoc Eq.refl) ▸ done

  b39 : Chain (Sw23 ∷ Toff203 ∷ CS12 ∷ Toff203 ∷ Sw12 ∷ CS12⁻ ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ Sw01 ∷ CS12 ∷ Toff203 ∷ CS12⁻ ∷ Sw23 ∷ [])
  b39 = at 4 2 (CS12⁻ ∷ Sw12 ∷ []) wn00019 ▸
       at 5 2 [] wn00014 ▸
       at 1 1 (Sw01 ∷ Toff213 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 2 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 3 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 4 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸ done

  b40 : Chain (Sw23 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ Sw01 ∷ CS12 ∷ Toff203 ∷ CS12⁻ ∷ Sw23 ∷ []) (Sw23 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ Sw01 ∷ Sw01 ∷ CS12 ∷ Toff203 ∷ CS12⁻ ∷ Sw23 ∷ [])
  b40 = at 5 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 8 2 (ι ∷ Sw01 ∷ []) wn00122 ▸ done

  b41 : Chain (Sw23 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ Sw01 ∷ Sw01 ∷ CS12 ∷ Toff203 ∷ CS12⁻ ∷ Sw23 ∷ []) (K3 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ Sw23 ∷ CS03 ∷ K2 ∷ ι ∷ CS12 ∷ Toff203 ∷ CS12⁻ ∷ Sw23 ∷ [])
  b41 = at 9 2 [] wn00031 ▸
       at 0 2 (K3 ∷ Sw23 ∷ []) wn00335 ▸
       at 1 2 (CS23 ∷ Sw23 ∷ []) wn00071 ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS23⁻ ∷ Sw23 ∷ []) wn00072 ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸ done

  b42 : Chain (K3 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ Sw23 ∷ CS03 ∷ K2 ∷ ι ∷ CS12 ∷ Toff203 ∷ CS12⁻ ∷ Sw23 ∷ []) (Sw01 ∷ K3 ∷ CS23 ∷ Sw01 ∷ Sw23 ∷ CX02 ∷ Sw23 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ K3 ∷ ι ∷ Sw23 ∷ CS12 ∷ Toff203 ∷ CS12⁻ ∷ Sw23 ∷ [])
  b42 = at 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 6 2 (K3 ∷ Sw23 ∷ []) wn00335 ▸
       at 7 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 0 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 1 2 (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑))) ▸
       at 2 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 4 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b43 : Chain (Sw01 ∷ K3 ∷ CS23 ∷ Sw01 ∷ Sw23 ∷ CX02 ∷ Sw23 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ K3 ∷ ι ∷ Sw23 ∷ CS12 ∷ Toff203 ∷ CS12⁻ ∷ Sw23 ∷ []) (Sw01 ∷ K3 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ Sw23 ∷ CX12 ∷ Sw01 ∷ Sw23 ∷ CS02 ∷ K3 ∷ ι ∷ Sw23 ∷ CS12 ∷ Toff203 ∷ CS12⁻ ∷ Sw23 ∷ [])
  b43 = at 3 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 4 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 3 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 6 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸ done

  b44 : Chain (Sw01 ∷ K3 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ Sw23 ∷ CX12 ∷ Sw01 ∷ Sw23 ∷ CS02 ∷ K3 ∷ ι ∷ Sw23 ∷ CS12 ∷ Toff203 ∷ CS12⁻ ∷ Sw23 ∷ []) (Toff302 ∷ Sw23 ∷ CS12 ∷ Toff203 ∷ CS12⁻ ∷ Sw23 ∷ [])
  b44 = at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 7 2 (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑))) ▸
       at 8 2 (ι1 ∷ Sw01 ∷ []) wn00124 ▸
       at 1 8 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) wn00385 ▸
       at 1 8 (Toff312 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff302 ∷ []) (by-assoc Eq.refl) ▸ done

  b45 : Chain (Toff302 ∷ Sw23 ∷ CS12 ∷ Toff203 ∷ CS12⁻ ∷ Sw23 ∷ []) (Toff302 ∷ CS13 ∷ Sw23 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ Sw01 ∷ CS12⁻ ∷ Sw23 ∷ [])
  b45 = at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw01 ∷ Toff213 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 4 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 5 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 6 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸ done

  b46 : Chain (Toff302 ∷ CS13 ∷ Sw23 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ Sw01 ∷ CS12⁻ ∷ Sw23 ∷ []) (Toff302 ∷ CS13 ∷ Sw23 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ Sw01 ∷ Sw01 ∷ CS12⁻ ∷ Sw23 ∷ [])
  b46 = at 7 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 10 2 (ι ∷ Sw01 ∷ []) wn00122 ▸ done

  b47 : Chain (Toff302 ∷ CS13 ∷ Sw23 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ Sw01 ∷ Sw01 ∷ CS12⁻ ∷ Sw23 ∷ []) (Toff302 ∷ CS13 ∷ K3 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ Sw23 ∷ CS03 ∷ K2 ∷ ι ∷ CS12⁻ ∷ Sw23 ∷ [])
  b47 = at 11 2 [] wn00031 ▸
       at 2 2 (K3 ∷ Sw23 ∷ []) wn00335 ▸
       at 3 2 (CS23 ∷ Sw23 ∷ []) wn00071 ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS23⁻ ∷ Sw23 ∷ []) wn00072 ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸ done

  b48 : Chain (Toff302 ∷ CS13 ∷ K3 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ Sw23 ∷ CS03 ∷ K2 ∷ ι ∷ CS12⁻ ∷ Sw23 ∷ []) (Toff302 ∷ CS13 ∷ Sw01 ∷ K3 ∷ CS23 ∷ Sw01 ∷ Sw23 ∷ CX02 ∷ Sw23 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ K3 ∷ ι ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ [])
  b48 = at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00003 ▸
       at 8 2 (K3 ∷ Sw23 ∷ []) wn00335 ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 3 2 (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑))) ▸
       at 4 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 6 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b49 : Chain (Toff302 ∷ CS13 ∷ Sw01 ∷ K3 ∷ CS23 ∷ Sw01 ∷ Sw23 ∷ CX02 ∷ Sw23 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ K3 ∷ ι ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (Toff302 ∷ CS13 ∷ Sw01 ∷ K3 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ Sw23 ∷ CX12 ∷ Sw01 ∷ Sw23 ∷ CS02 ∷ K3 ∷ ι ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ [])
  b49 = at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 8 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸ done

  b50 : Chain (Toff302 ∷ CS13 ∷ Sw01 ∷ K3 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ Sw23 ∷ CX12 ∷ Sw01 ∷ Sw23 ∷ CS02 ∷ K3 ∷ ι ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (Toff302 ∷ CS13 ∷ Toff302 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ [])
  b50 = at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 9 2 (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑))) ▸
       at 10 2 (ι1 ∷ Sw01 ∷ []) wn00124 ▸
       at 3 8 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) wn00385 ▸
       at 3 8 (Toff312 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff302 ∷ []) (by-assoc Eq.refl) ▸ done

  b51 : Chain (Toff302 ∷ CS13 ∷ Toff302 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b51 = at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸ done

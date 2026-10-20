{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D769 where

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
open import Examples.Groups.Clifford+CS.Four.Wins.W01 using (wn00005 ; wn00007 ; wn00008 ; wn00009 ; wn00010 ; wn00012 ; wn00014 ; wn00015 ; wn00016 ; wn00018 ; wn00019 ; wn00025 ; wn00027 ; wn00028 ; wn00029 ; wn00031 ; wn00047 ; wn00048 ; wn00123 ; wn00124 ; wn00127)
open import Examples.Groups.Clifford+CS.Four.Wins.W02 using (wn00271 ; wn00272 ; wn00274 ; wn00311 ; wn00312 ; wn00338 ; wn00339 ; wn00340 ; wn00363 ; wn00366 ; wn00398)
open import Examples.Groups.Clifford+CS.Four.Wins.W03 using (wn00477)
open import Examples.Groups.Clifford+CS.Four.Wins.W24 using (wn01207)
open import Examples.Groups.Clifford+CS.Four.Wins.W35 using (wn01731)
open import Examples.Groups.Clifford+CS.Four.Wins.W48 using (wn02549)
open import Examples.Groups.Clifford+CS.Four.Wins.W49 using (wn02573 ; wn02574)
open import Examples.Groups.Clifford+CS.Four.D.D760 using (lem-merge-R0)

-- merge R0 @1023: 91 steps
lem-merge-R0-at1023 : ⟪ (S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ S1 ∷ Toff102 ∷ S1⁻ ∷ []) ⟫ʷ
lem-merge-R0-at1023 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (run b11)))))))))))
  where
  b0 : Chain (S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) (S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw01 ∷ CS12 ∷ K0 ∷ ι1 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ Sw01 ∷ [])
  b0 = at 18 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 17 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸
       at 16 2 (Sw01 ∷ S0⁻ ∷ []) wn02549 ▸
       at 15 2 (Sw01 ∷ K0⁻ ∷ []) wn01731 ▸
       at 14 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 21 2 (Sw01 ∷ ι1 ∷ []) wn00127 ▸
       at 20 2 (Sw01 ∷ K0 ∷ []) wn00271 ▸
       at 19 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸ done

  b1 : Chain (S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw01 ∷ CS12 ∷ K0 ∷ ι1 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ Sw01 ∷ []) (S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw01 ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ Sw01 ∷ [])
  b1 = at 18 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 17 2 (Sw01 ∷ CS02⁻ ∷ []) wn00009 ▸
       at 16 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 15 2 (Sw01 ∷ CS02 ∷ []) wn00010 ▸
       at 14 2 (Sw01 ∷ K0 ∷ []) wn00271 ▸
       at 15 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) wn00272 ▸
       at 15 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 13 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw01 ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ Sw01 ∷ []) (S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw01 ∷ CS12 ∷ K0 ∷ ι1 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ Sw01 ∷ [])
  b2 = at 15 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 14 2 (Sw01 ∷ CS02⁻ ∷ []) wn00009 ▸
       at 13 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 14 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 12 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 19 2 (Sw01 ∷ ι1 ∷ []) wn00127 ▸
       at 18 2 (Sw01 ∷ K0 ∷ []) wn00271 ▸
       at 17 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸ done

  b3 : Chain (S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw01 ∷ CS12 ∷ K0 ∷ ι1 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ Sw01 ∷ []) (S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ S1 ∷ K1 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ Sw01 ∷ [])
  b3 = at 16 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 15 2 (Sw01 ∷ CS02⁻ ∷ []) wn00009 ▸
       at 14 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 13 2 (Sw01 ∷ CS02 ∷ []) wn00010 ▸
       at 12 2 (Sw01 ∷ K0 ∷ []) wn00271 ▸
       at 13 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) wn00272 ▸
       at 13 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ S1 ∷ K1 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ Sw01 ∷ []) (S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ Sw01 ∷ S0⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ Sw01 ∷ [])
  b4 = at 13 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 12 2 (Sw01 ∷ CS02 ∷ []) wn00010 ▸
       at 11 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 12 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw01 ∷ K0 ∷ []) wn00271 ▸
       at 9 2 (Sw01 ∷ S0 ∷ []) wn01207 ▸
       at 8 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸
       at 7 2 (Sw01 ∷ S0⁻ ∷ []) wn02549 ▸ done

  b5 : Chain (S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ Sw01 ∷ S0⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ Sw01 ∷ []) (S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ CS12 ∷ Sw01 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K0 ∷ ι1 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ Sw01 ∷ [])
  b5 = at 6 2 (Sw01 ∷ K0⁻ ∷ []) wn01731 ▸
       at 5 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (Sw01 ∷ ι1 ∷ []) wn00127 ▸
       at 11 2 (Sw01 ∷ K0 ∷ []) wn00271 ▸
       at 10 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 9 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 8 2 (Sw01 ∷ CS02⁻ ∷ []) wn00009 ▸
       at 7 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸ done

  b6 : Chain (S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ CS12 ∷ Sw01 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K0 ∷ ι1 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ Sw01 ∷ []) (S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ Sw01 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ Sw01 ∷ [])
  b6 = at 6 2 (Sw01 ∷ CS02 ∷ []) wn00010 ▸
       at 5 2 (Sw01 ∷ K0 ∷ []) wn00271 ▸
       at 6 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) wn00272 ▸
       at 6 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 5 2 (Sw01 ∷ CS02⁻ ∷ []) wn00009 ▸
       at 4 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b7 : Chain (S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ Sw01 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ Sw01 ∷ []) (S1 ∷ K1 ∷ CS13 ∷ K1 ∷ CS12 ∷ Sw01 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K0 ∷ ι1 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ Sw01 ∷ [])
  b7 = at 5 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw01 ∷ ι1 ∷ []) wn00127 ▸
       at 9 2 (Sw01 ∷ K0 ∷ []) wn00271 ▸
       at 8 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 7 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 6 2 (Sw01 ∷ CS02⁻ ∷ []) wn00009 ▸
       at 5 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸ done

  b8 : Chain (S1 ∷ K1 ∷ CS13 ∷ K1 ∷ CS12 ∷ Sw01 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K0 ∷ ι1 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ Sw01 ∷ []) (S1 ∷ K1 ∷ Sw01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ Sw01 ∷ [])
  b8 = at 4 2 (Sw01 ∷ CS02 ∷ []) wn00010 ▸
       at 3 2 (Sw01 ∷ K0 ∷ []) wn00271 ▸
       at 4 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) wn00272 ▸
       at 4 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 3 2 (Sw01 ∷ CS02 ∷ []) wn00010 ▸
       at 2 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b9 : Chain (S1 ∷ K1 ∷ Sw01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ Sw01 ∷ []) (CS02⁻ ∷ S1 ∷ K1 ∷ Sw01 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ S0⁻ ∷ Sw01 ∷ [])
  b9 = at 3 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw01 ∷ K0 ∷ []) wn00271 ▸
       at 0 2 (Sw01 ∷ S0 ∷ []) wn01207 ▸
       at 1 18 (CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ []) (lem-merge-R0) ▸
       at 0 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸
       at 1 2 (S1 ∷ Sw01 ∷ []) wn00311 ▸
       at 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (K1 ∷ Sw01 ∷ []) wn00123 ▸ done

  b10 : Chain (CS02⁻ ∷ S1 ∷ K1 ∷ Sw01 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ S0⁻ ∷ Sw01 ∷ []) (CS02⁻ ∷ S1 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw01 ∷ S0⁻ ∷ Sw01 ∷ [])
  b10 = at 3 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 4 2 (CX10 ∷ Sw01 ∷ []) wn00028 ▸
       at 5 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸
       at 6 2 (CX10 ∷ Sw01 ∷ []) wn00028 ▸
       at 7 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 8 2 (K1 ∷ Sw01 ∷ []) wn00123 ▸
       at 9 2 (ι1 ∷ Sw01 ∷ []) wn00124 ▸
       at 2 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) wn00274 ▸ done

  b11 : Chain (CS02⁻ ∷ S1 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw01 ∷ S0⁻ ∷ Sw01 ∷ []) (CS02⁻ ∷ S1 ∷ Toff102 ∷ S1⁻ ∷ [])
  b11 = at 2 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (S1⁻ ∷ Sw01 ∷ []) wn00312 ▸
       at 4 2 [] wn00031 ▸ done

-- merge R0 @2013: 181 steps
lem-merge-R0-at2013 : ⟪ (S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ X3 ∷ S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ []) ⟫ʷ
lem-merge-R0-at2013 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (run b22))))))))))))))))))))))
  where
  b0 : Chain (S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ X3 ∷ S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ X3 ∷ []) (S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ X3 ∷ S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw12 ∷ K1 ∷ ι ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ Sw12 ∷ [])
  b0 = at 18 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 17 2 (Sw12 ∷ X3 ∷ []) (sym (low₃-comm ((Swap ↑)) (X))) ▸
       at 16 2 (Sw12 ∷ S1⁻ ∷ []) wn02573 ▸
       at 15 2 (Sw12 ∷ K1⁻ ∷ []) wn02574 ▸
       at 14 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 21 2 (Sw12 ∷ ι ∷ []) (low₁-comm (iI) (Swap)) ▸
       at 20 2 (Sw12 ∷ K1 ∷ []) wn00398 ▸
       at 19 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ X3 ∷ S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw12 ∷ K1 ∷ ι ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ Sw12 ∷ []) (S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ X3 ∷ S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Sw12 ∷ K1 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K1 ∷ ι ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ Sw12 ∷ [])
  b1 = at 21 2 [] wn00014 ▸
       at 18 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 19 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 17 2 (Sw12 ∷ CS12⁻ ∷ []) wn00015 ▸
       at 16 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 17 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 (Sw12 ∷ CS12 ∷ []) wn00016 ▸
       at 14 2 (Sw12 ∷ K1 ∷ []) wn00398 ▸ done

  b2 : Chain (S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ X3 ∷ S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Sw12 ∷ K1 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K1 ∷ ι ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ Sw12 ∷ []) (S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ X3 ∷ S2 ∷ K2 ∷ CS23 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw12 ∷ CS01 ∷ K1 ∷ ι ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ Sw12 ∷ [])
  b2 = at 15 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) wn00366 ▸
       at 15 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (Sw12 ∷ CS13⁻ ∷ []) wn00047 ▸
       at 12 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 19 2 (Sw12 ∷ ι ∷ []) (low₁-comm (iI) (Swap)) ▸
       at 18 2 (Sw12 ∷ K1 ∷ []) wn00398 ▸
       at 17 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 19 2 [] wn00014 ▸ done

  b3 : Chain (S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ X3 ∷ S2 ∷ K2 ∷ CS23 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw12 ∷ CS01 ∷ K1 ∷ ι ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ Sw12 ∷ []) (S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ X3 ∷ S2 ∷ K2 ∷ CS23 ∷ Sw12 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ Sw12 ∷ [])
  b3 = at 16 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 17 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 (Sw12 ∷ CS12⁻ ∷ []) wn00015 ▸
       at 14 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 15 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (Sw12 ∷ CS12 ∷ []) wn00016 ▸
       at 12 2 (Sw12 ∷ K1 ∷ []) wn00398 ▸
       at 13 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) wn00366 ▸ done

  b4 : Chain (S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ X3 ∷ S2 ∷ K2 ∷ CS23 ∷ Sw12 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ Sw12 ∷ []) (S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw12 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ Sw12 ∷ [])
  b4 = at 13 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (Sw12 ∷ CS13 ∷ []) wn00048 ▸
       at 10 2 (Sw12 ∷ K1 ∷ []) wn00398 ▸
       at 9 2 (Sw12 ∷ S1 ∷ []) wn00477 ▸
       at 8 2 (Sw12 ∷ X3 ∷ []) (sym (low₃-comm ((Swap ↑)) (X))) ▸
       at 7 2 (Sw12 ∷ S1⁻ ∷ []) wn02573 ▸
       at 6 2 (Sw12 ∷ K1⁻ ∷ []) wn02574 ▸
       at 5 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸ done

  b5 : Chain (S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw12 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ Sw12 ∷ []) (S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ K2 ∷ CS12 ∷ Sw12 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K1 ∷ ι ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ Sw12 ∷ [])
  b5 = at 12 2 (Sw12 ∷ ι ∷ []) (low₁-comm (iI) (Swap)) ▸
       at 11 2 (Sw12 ∷ K1 ∷ []) wn00398 ▸
       at 10 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] wn00014 ▸
       at 9 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 10 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw12 ∷ CS12⁻ ∷ []) wn00015 ▸
       at 7 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸ done

  b6 : Chain (S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ K2 ∷ CS12 ∷ Sw12 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K1 ∷ ι ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ Sw12 ∷ []) (S2 ∷ K2 ∷ CS23 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ Sw12 ∷ ι ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ Sw12 ∷ [])
  b6 = at 8 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw12 ∷ CS12 ∷ []) wn00016 ▸
       at 5 2 (Sw12 ∷ K1 ∷ []) wn00398 ▸
       at 6 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) wn00366 ▸
       at 6 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw12 ∷ CS13⁻ ∷ []) wn00047 ▸
       at 3 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw12 ∷ ι ∷ []) (low₁-comm (iI) (Swap)) ▸ done

  b7 : Chain (S2 ∷ K2 ∷ CS23 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ Sw12 ∷ ι ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ Sw12 ∷ []) (S2 ∷ K2 ∷ CS23 ∷ K2 ∷ CS12 ∷ Sw12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K1 ∷ ι ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ Sw12 ∷ [])
  b7 = at 9 2 (Sw12 ∷ K1 ∷ []) wn00398 ▸
       at 8 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00014 ▸
       at 7 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 8 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw12 ∷ CS12⁻ ∷ []) wn00015 ▸
       at 5 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 6 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸ done

  b8 : Chain (S2 ∷ K2 ∷ CS23 ∷ K2 ∷ CS12 ∷ Sw12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K1 ∷ ι ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ Sw12 ∷ []) (Sw12 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b8 = at 4 2 (Sw12 ∷ CS12 ∷ []) wn00016 ▸
       at 3 2 (Sw12 ∷ K1 ∷ []) wn00398 ▸
       at 4 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) wn00366 ▸
       at 4 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw12 ∷ CS13 ∷ []) wn00048 ▸
       at 1 2 (Sw12 ∷ K1 ∷ []) wn00398 ▸
       at 0 2 (Sw12 ∷ S1 ∷ []) wn00477 ▸
       at 19 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸ done

  b9 : Chain (Sw12 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw01 ∷ CX10 ∷ CS12 ∷ K0 ∷ ι1 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ Sw01 ∷ Sw12 ∷ [])
  b9 = at 18 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸
       at 17 2 (Sw01 ∷ S0⁻ ∷ []) wn02549 ▸
       at 16 2 (Sw01 ∷ K0⁻ ∷ []) wn01731 ▸
       at 15 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 22 2 (Sw01 ∷ ι1 ∷ []) wn00127 ▸
       at 21 2 (Sw01 ∷ K0 ∷ []) wn00271 ▸
       at 20 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 19 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸ done

  b10 : Chain (Sw12 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw01 ∷ CX10 ∷ CS12 ∷ K0 ∷ ι1 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ Sw23 ∷ CS12⁻ ∷ Sw01 ∷ Sw23 ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ Sw01 ∷ Sw12 ∷ [])
  b10 = at 18 2 (Sw01 ∷ CS02⁻ ∷ []) wn00009 ▸
       at 17 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 16 2 (Sw01 ∷ CS02 ∷ []) wn00010 ▸
       at 15 2 (Sw01 ∷ K0 ∷ []) wn00271 ▸
       at 16 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) wn00272 ▸
       at 16 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 14 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 16 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b11 : Chain (Sw12 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ Sw23 ∷ CS12⁻ ∷ Sw01 ∷ Sw23 ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw01 ∷ CX10 ∷ CS12 ∷ K0 ∷ ι1 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ Sw01 ∷ Sw12 ∷ [])
  b11 = at 15 2 (Sw01 ∷ CS02⁻ ∷ []) wn00009 ▸
       at 14 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 15 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 13 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 20 2 (Sw01 ∷ ι1 ∷ []) wn00127 ▸
       at 19 2 (Sw01 ∷ K0 ∷ []) wn00271 ▸
       at 18 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 17 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸ done

  b12 : Chain (Sw12 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw01 ∷ CX10 ∷ CS12 ∷ K0 ∷ ι1 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ S1 ∷ K1 ∷ Sw23 ∷ CS12 ∷ Sw01 ∷ Sw23 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ Sw01 ∷ Sw12 ∷ [])
  b12 = at 16 2 (Sw01 ∷ CS02⁻ ∷ []) wn00009 ▸
       at 15 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 14 2 (Sw01 ∷ CS02 ∷ []) wn00010 ▸
       at 13 2 (Sw01 ∷ K0 ∷ []) wn00271 ▸
       at 14 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) wn00272 ▸
       at 14 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b13 : Chain (Sw12 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ S1 ∷ K1 ∷ Sw23 ∷ CS12 ∷ Sw01 ∷ Sw23 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ Sw01 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ Sw01 ∷ Sw12 ∷ [])
  b13 = at 13 2 (Sw01 ∷ CS02 ∷ []) wn00010 ▸
       at 12 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 13 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (Sw01 ∷ K0 ∷ []) wn00271 ▸
       at 10 2 (Sw01 ∷ S0 ∷ []) wn01207 ▸
       at 9 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸
       at 8 2 (Sw01 ∷ S0⁻ ∷ []) wn02549 ▸
       at 7 2 (Sw01 ∷ K0⁻ ∷ []) wn01731 ▸ done

  b14 : Chain (Sw12 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ Sw01 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ Sw01 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K0 ∷ ι1 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ Sw01 ∷ Sw12 ∷ [])
  b14 = at 6 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (Sw01 ∷ ι1 ∷ []) wn00127 ▸
       at 12 2 (Sw01 ∷ K0 ∷ []) wn00271 ▸
       at 11 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 10 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 9 2 (Sw01 ∷ CS02⁻ ∷ []) wn00009 ▸
       at 8 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 7 2 (Sw01 ∷ CS02 ∷ []) wn00010 ▸ done

  b15 : Chain (Sw12 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ Sw01 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K0 ∷ ι1 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ Sw01 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ Sw01 ∷ Sw12 ∷ [])
  b15 = at 6 2 (Sw01 ∷ K0 ∷ []) wn00271 ▸
       at 7 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) wn00272 ▸
       at 7 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 6 2 (Sw01 ∷ CS02⁻ ∷ []) wn00009 ▸
       at 5 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 6 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b16 : Chain (Sw12 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ Sw01 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ S1 ∷ K1 ∷ CS13 ∷ K1 ∷ Sw01 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K0 ∷ ι1 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ Sw01 ∷ Sw12 ∷ [])
  b16 = at 4 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (Sw01 ∷ ι1 ∷ []) wn00127 ▸
       at 10 2 (Sw01 ∷ K0 ∷ []) wn00271 ▸
       at 9 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 8 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 7 2 (Sw01 ∷ CS02⁻ ∷ []) wn00009 ▸
       at 6 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 5 2 (Sw01 ∷ CS02 ∷ []) wn00010 ▸ done

  b17 : Chain (Sw12 ∷ S1 ∷ K1 ∷ CS13 ∷ K1 ∷ Sw01 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K0 ∷ ι1 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ S1 ∷ K1 ∷ Sw01 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ Sw01 ∷ Sw12 ∷ [])
  b17 = at 4 2 (Sw01 ∷ K0 ∷ []) wn00271 ▸
       at 5 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) wn00272 ▸
       at 5 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 4 2 (Sw01 ∷ CS02 ∷ []) wn00010 ▸
       at 3 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 4 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b18 : Chain (Sw12 ∷ S1 ∷ K1 ∷ Sw01 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ CS02⁻ ∷ S1 ∷ K1 ∷ CS02 ∷ Sw01 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ S0⁻ ∷ Sw01 ∷ Sw12 ∷ [])
  b18 = at 2 2 (Sw01 ∷ K0 ∷ []) wn00271 ▸
       at 1 2 (Sw01 ∷ S0 ∷ []) wn01207 ▸
       at 2 18 (CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ []) (lem-merge-R0) ▸
       at 1 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸
       at 2 2 (S1 ∷ Sw01 ∷ []) wn00311 ▸
       at 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (K1 ∷ Sw01 ∷ []) wn00123 ▸
       at 4 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸ done

  b19 : Chain (Sw12 ∷ CS02⁻ ∷ S1 ∷ K1 ∷ CS02 ∷ Sw01 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ S0⁻ ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ CS02⁻ ∷ S1 ∷ Toff102 ∷ Sw01 ∷ S0⁻ ∷ Sw01 ∷ Sw12 ∷ [])
  b19 = at 5 2 (CX10 ∷ Sw01 ∷ []) wn00028 ▸
       at 6 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸
       at 7 2 (CX10 ∷ Sw01 ∷ []) wn00028 ▸
       at 8 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 9 2 (K1 ∷ Sw01 ∷ []) wn00123 ▸
       at 10 2 (ι1 ∷ Sw01 ∷ []) wn00124 ▸
       at 3 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) wn00274 ▸
       at 3 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸ done

  b20 : Chain (Sw12 ∷ CS02⁻ ∷ S1 ∷ Toff102 ∷ Sw01 ∷ S0⁻ ∷ Sw01 ∷ Sw12 ∷ []) (CS01⁻ ∷ S2 ∷ K2 ∷ CS12 ∷ Sw12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ S1⁻ ∷ Sw12 ∷ [])
  b20 = at 4 2 (S1⁻ ∷ Sw01 ∷ []) wn00312 ▸
       at 5 2 [] wn00031 ▸
       at 1 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] wn00014 ▸
       at 1 2 (S2 ∷ Sw12 ∷ []) wn00338 ▸
       at 3 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (K2 ∷ Sw12 ∷ []) wn00340 ▸
       at 3 2 (CS12 ∷ Sw12 ∷ []) wn00018 ▸ done

  b21 : Chain (CS01⁻ ∷ S2 ∷ K2 ∷ CS12 ∷ Sw12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ S1⁻ ∷ Sw12 ∷ []) (CS01⁻ ∷ S2 ∷ K2 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K2 ∷ Sw12 ∷ ι ∷ S1⁻ ∷ Sw12 ∷ [])
  b21 = at 6 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS12⁻ ∷ Sw12 ∷ []) wn00019 ▸
       at 8 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 6 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 8 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00014 ▸
       at 8 2 (K2 ∷ Sw12 ∷ []) wn00340 ▸ done

  b22 : Chain (CS01⁻ ∷ S2 ∷ K2 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K2 ∷ Sw12 ∷ ι ∷ S1⁻ ∷ Sw12 ∷ []) (CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ [])
  b22 = at 9 2 (ι ∷ Sw12 ∷ []) (sym (low₁-comm (iI) (Swap))) ▸
       at 2 8 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) wn00363 ▸
       at 2 8 (Toff201 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (S2⁻ ∷ Sw12 ∷ []) wn00339 ▸
       at 4 2 [] wn00014 ▸ done

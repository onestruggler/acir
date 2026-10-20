{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D003 where

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
open import Examples.Groups.Clifford+CS.Four.Wins.W01 using (wn00001 ; wn00002 ; wn00003 ; wn00004 ; wn00005 ; wn00006 ; wn00007 ; wn00008 ; wn00009 ; wn00010 ; wn00011 ; wn00012 ; wn00013 ; wn00014 ; wn00015 ; wn00016 ; wn00017 ; wn00018 ; wn00019 ; wn00020 ; wn00021 ; wn00022 ; wn00023 ; wn00024 ; wn00025 ; wn00026 ; wn00027 ; wn00028 ; wn00029 ; wn00030 ; wn00031 ; wn00032 ; wn00033 ; wn00047 ; wn00048 ; wn00064 ; wn00065 ; wn00068 ; wn00075 ; wn00078 ; wn00081 ; wn00084 ; wn00085 ; wn00089 ; wn00091 ; wn00092 ; wn00093 ; wn00094 ; wn00095 ; wn00096 ; wn00097 ; wn00098 ; wn00099)

-- comm CCZ123 CS03: 57 steps
lem-comm-CCZ123-CS03 : ⟪ (CCZ123 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ CCZ123 ∷ []) ⟫ʷ
lem-comm-CCZ123-CS03 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (CCZ123 ∷ CS03 ∷ []) (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ Sw01 ∷ CS23 ∷ CS13 ∷ Sw01 ∷ [])
  b0 = at 0 1 (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) wn00075 ▸
       at 6 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 6 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 5 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸ done

  b1 : Chain (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ Sw01 ∷ CS23 ∷ CS13 ∷ Sw01 ∷ []) (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS03 ∷ CS23 ∷ [])
  b1 = at 5 2 (CS13 ∷ CS23 ∷ []) wn00091 ▸
       at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 4 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 6 2 [] wn00031 ▸ done

  b2 : Chain (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS03 ∷ CS23 ∷ []) (CS12 ∷ CX31 ∷ CS12⁻ ∷ CS03 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ CS23 ∷ [])
  b2 = at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸
       at 3 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 4 2 (CS02 ∷ CX21 ∷ []) wn00092 ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (CS12 ∷ CX31 ∷ CS12⁻ ∷ CS03 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ CS23 ∷ []) (CS12 ∷ CX31 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ CS23⁻ ∷ Sw12 ∷ Sw23 ∷ CX31 ∷ CS23 ∷ [])
  b3 = at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 3 (CX31 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 3 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw12 ∷ CS23⁻ ∷ []) wn00084 ▸
       at 4 2 (CS01 ∷ CS23⁻ ∷ []) (sym (low-comm (CS) ((CS • CS • CS)))) ▸ done

  b4 : Chain (CS12 ∷ CX31 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ CS23⁻ ∷ Sw12 ∷ Sw23 ∷ CX31 ∷ CS23 ∷ []) (CS12 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ [])
  b4 = at 5 2 (Sw12 ∷ CS13⁻ ∷ []) wn00047 ▸
       at 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00003 ▸
       at 2 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸
       at 1 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b5 : Chain (CS12 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) (CS12 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ [])
  b5 = at 3 2 [] wn00003 ▸
       at 2 2 (CS02 ∷ CX21 ∷ []) wn00092 ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CX31 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸
       at 1 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b6 : Chain (CS12 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) (CS03 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ [])
  b6 = at 0 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw12 ∷ CS23 ∷ []) wn00065 ▸
       at 2 2 (CS01 ∷ CS23 ∷ []) (sym (low-comm (CS) (CS))) ▸
       at 3 2 (Sw12 ∷ CS13 ∷ []) wn00048 ▸
       at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸
       at 0 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b7 : Chain (CS03 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) (CS03 ∷ CCZ123 ∷ [])
  b7 = at 1 5 (CCZ123 ∷ []) wn00081 ▸ done

-- comm CCZ012 CS03: 53 steps
lem-comm-CCZ012-CS03 : ⟪ (CCZ012 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ CCZ012 ∷ []) ⟫ʷ
lem-comm-CCZ012-CS03 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (run b6))))))
  where
  b0 : Chain (CCZ012 ∷ CS03 ∷ []) (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ Sw01 ∷ CS12 ∷ CS13 ∷ Sw01 ∷ [])
  b0 = at 0 1 (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) wn00085 ▸
       at 6 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 6 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 5 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸ done

  b1 : Chain (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ Sw01 ∷ CS12 ∷ CS13 ∷ Sw01 ∷ []) (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS03 ∷ CS02 ∷ [])
  b1 = at 5 2 (CS13 ∷ CS12 ∷ []) wn00093 ▸
       at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 4 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 6 2 [] wn00031 ▸ done

  b2 : Chain (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS03 ∷ CS02 ∷ []) (CS01 ∷ CX21 ∷ CS01⁻ ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ CX21 ∷ CS02 ∷ [])
  b2 = at 4 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 3 (CX31 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw12 ∷ CX32 ∷ []) wn00013 ▸
       at 5 2 (CS01 ∷ CX32 ∷ []) (sym (low-comm (CS) (CX₁₀))) ▸
       at 6 2 (Sw12 ∷ CX31 ∷ []) wn00078 ▸
       at 7 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00003 ▸ done

  b3 : Chain (CS01 ∷ CX21 ∷ CS01⁻ ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ CX21 ∷ CS02 ∷ []) (CS01 ∷ CX21 ∷ CS03 ∷ Sw23 ∷ CS01⁻ ∷ Sw23 ∷ CX21 ∷ CS02 ∷ [])
  b3 = at 3 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 2 2 (Sw23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (Swap)) ▸
       at 3 2 (CS02 ∷ CS01⁻ ∷ []) wn00094 ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (CS01 ∷ CX21 ∷ CS03 ∷ Sw23 ∷ CS01⁻ ∷ Sw23 ∷ CX21 ∷ CS02 ∷ []) (CS01 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ CX31 ∷ Sw23 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ [])
  b4 = at 3 2 (CS01⁻ ∷ Sw23 ∷ []) (sym (low-comm ((CS • CS • CS)) (Swap))) ▸
       at 4 2 [] wn00003 ▸
       at 2 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CX31 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw12 ∷ CX32 ∷ []) wn00013 ▸
       at 3 2 (CS01 ∷ CX32 ∷ []) (sym (low-comm (CS) (CX₁₀))) ▸
       at 4 2 (Sw12 ∷ CX31 ∷ []) wn00078 ▸ done

  b5 : Chain (CS01 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ CX31 ∷ Sw23 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) (Sw23 ∷ CS02 ∷ CS01 ∷ Sw23 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ [])
  b5 = at 5 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00003 ▸
       at 1 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸
       at 0 2 (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap)) ▸
       at 1 2 (CS02 ∷ CS01 ∷ []) wn00095 ▸ done

  b6 : Chain (Sw23 ∷ CS02 ∷ CS01 ∷ Sw23 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) (CS03 ∷ CCZ012 ∷ [])
  b6 = at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 0 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 2 2 [] wn00003 ▸
       at 1 5 (CCZ012 ∷ []) wn00089 ▸ done

-- CZ13 passes T: 25 steps
lem-CZ13-passes-T : ⟪ (CZ13 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CZ13 ∷ []) ⟫ʷ
lem-CZ13-passes-T = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (CZ13 ∷ Toff012 ∷ []) (K0 ∷ CS02 ∷ CX12 ∷ CZ13 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K0⁻ ∷ [])
  b0 = at 1 1 (K0 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K0⁻ ∷ []) wn00064 ▸
       at 0 2 (K0 ∷ CZ13 ∷ []) (sym (low₁-comm (K) ((Swap ↑ • CZ • Swap ↑)))) ▸
       at 2 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw12 ∷ CZ23 ∷ []) wn00096 ▸
       at 2 2 (CS01 ∷ CZ23 ∷ []) (sym (low-comm (CS) (CZ))) ▸
       at 3 2 (Sw12 ∷ CZ13 ∷ []) wn00097 ▸
       at 1 3 (CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CX12 ∷ CZ13 ∷ []) wn00098 ▸ done

  b1 : Chain (K0 ∷ CS02 ∷ CX12 ∷ CZ13 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K0⁻ ∷ []) (K0 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CZ13 ∷ Sw23 ∷ CS01 ∷ Sw23 ∷ K0⁻ ∷ [])
  b1 = at 4 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw12 ∷ CZ23 ∷ []) wn00096 ▸
       at 4 2 (CS01⁻ ∷ CZ23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CZ))) ▸
       at 5 2 (Sw12 ∷ CZ13 ∷ []) wn00097 ▸
       at 3 3 (CS02⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX12 ∷ CZ13 ∷ []) wn00098 ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 2 (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap)) ▸ done

  b2 : Chain (K0 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CZ13 ∷ Sw23 ∷ CS01 ∷ Sw23 ∷ K0⁻ ∷ []) (K0 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K0⁻ ∷ CZ13 ∷ [])
  b2 = at 5 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00003 ▸
       at 6 2 (CS01 ∷ CZ12 ∷ []) wn00099 ▸
       at 5 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00003 ▸
       at 6 2 (K0⁻ ∷ CZ13 ∷ []) (sym (low₁-comm ((K • iI)) ((Swap ↑ • CZ • Swap ↑)))) ▸ done

  b3 : Chain (K0 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K0⁻ ∷ CZ13 ∷ []) (Toff012 ∷ CZ13 ∷ [])
  b3 = at 0 7 (Toff012 ∷ []) wn00068 ▸ done

-- comm CCZ123 CCZ012: 243 steps
lem-comm-CCZ123-CCZ012 : ⟪ (CCZ123 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ CCZ123 ∷ []) ⟫ʷ
lem-comm-CCZ123-CCZ012 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (run b30))))))))))))))))))))))))))))))
  where
  b0 : Chain (CCZ123 ∷ CCZ012 ∷ []) (CCZ123 ∷ CCZ012 ∷ CX30 ∷ CCZ012 ∷ CCZ012 ∷ CX30 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 0 (CX20 ∷ CX20 ∷ []) wn00002 ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸
       at 3 0 (CCZ012 ∷ CCZ012 ∷ []) wn00004 ▸ done

  b1 : Chain (CCZ123 ∷ CCZ012 ∷ CX30 ∷ CCZ012 ∷ CCZ012 ∷ CX30 ∷ []) (CCZ123 ∷ CCZ012 ∷ CX30 ∷ CCZ012 ∷ CX30 ∷ Sw01 ∷ Sw01 ∷ CX30 ∷ CCZ012 ∷ CX30 ∷ [])
  b1 = at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 0 (CX20 ∷ CX20 ∷ []) wn00002 ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸
       at 5 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸ done

  b2 : Chain (CCZ123 ∷ CCZ012 ∷ CX30 ∷ CCZ012 ∷ CX30 ∷ Sw01 ∷ Sw01 ∷ CX30 ∷ CCZ012 ∷ CX30 ∷ []) (CCZ123 ∷ CCZ012 ∷ CX30 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw01 ∷ CX10 ∷ CS12 ∷ CX31 ∷ Sw01 ∷ CX30 ∷ CCZ012 ∷ CX30 ∷ [])
  b2 = at 4 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 5 2 (Sw01 ∷ CX21 ∷ []) wn00006 ▸
       at 4 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 5 3 (CX31 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 6 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸ done

  b3 : Chain (CCZ123 ∷ CCZ012 ∷ CX30 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw01 ∷ CX10 ∷ CS12 ∷ CX31 ∷ Sw01 ∷ CX30 ∷ CCZ012 ∷ CX30 ∷ []) (CCZ123 ∷ CCZ012 ∷ Sw23 ∷ Sw01 ∷ CX21 ∷ Sw23 ∷ CCZ012 ∷ CX31 ∷ Sw01 ∷ CX30 ∷ CCZ012 ∷ CX30 ∷ [])
  b3 = at 5 2 (Sw01 ∷ CS02⁻ ∷ []) wn00009 ▸
       at 4 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 3 2 (Sw01 ∷ CS02 ∷ []) wn00010 ▸
       at 4 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00011 ▸
       at 4 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 3 2 (Sw01 ∷ CX21 ∷ []) wn00006 ▸ done

  b4 : Chain (CCZ123 ∷ CCZ012 ∷ Sw23 ∷ Sw01 ∷ CX21 ∷ Sw23 ∷ CCZ012 ∷ CX31 ∷ Sw01 ∷ CX30 ∷ CCZ012 ∷ CX30 ∷ []) (CCZ123 ∷ CCZ012 ∷ Sw01 ∷ CX31 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw12 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ CS01 ∷ CX32 ∷ Sw12 ∷ Sw01 ∷ CX30 ∷ CCZ012 ∷ CX30 ∷ [])
  b4 = at 2 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 3 3 (CX31 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 5 2 (Sw12 ∷ CX32 ∷ []) wn00013 ▸
       at 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 8 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00014 ▸
       at 7 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸ done

  b5 : Chain (CCZ123 ∷ CCZ012 ∷ Sw01 ∷ CX31 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw12 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ CS01 ∷ CX32 ∷ Sw12 ∷ Sw01 ∷ CX30 ∷ CCZ012 ∷ CX30 ∷ []) (CCZ123 ∷ CCZ012 ∷ Sw01 ∷ Sw12 ∷ CX32 ∷ CCZ012 ∷ CX32 ∷ Sw12 ∷ Sw01 ∷ CX30 ∷ CCZ012 ∷ CX30 ∷ [])
  b5 = at 8 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw12 ∷ CS12⁻ ∷ []) wn00015 ▸
       at 5 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 6 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw12 ∷ CS12 ∷ []) wn00016 ▸
       at 5 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00017 ▸
       at 5 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw12 ∷ CX32 ∷ []) wn00013 ▸ done

  b6 : Chain (CCZ123 ∷ CCZ012 ∷ Sw01 ∷ Sw12 ∷ CX32 ∷ CCZ012 ∷ CX32 ∷ Sw12 ∷ Sw01 ∷ CX30 ∷ CCZ012 ∷ CX30 ∷ []) (CCZ123 ∷ CCZ012 ∷ Sw01 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ Sw12 ∷ CS02 ∷ CCZ013 ∷ Sw12 ∷ Sw01 ∷ CX30 ∷ CCZ012 ∷ CX30 ∷ [])
  b6 = at 4 3 (CCZ012 ∷ CCZ013 ∷ []) (ax cx-ccz) ▸
       at 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS12 ∷ Sw12 ∷ []) wn00018 ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS12⁻ ∷ Sw12 ∷ []) wn00019 ▸
       at 8 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 6 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸ done

  b7 : Chain (CCZ123 ∷ CCZ012 ∷ Sw01 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ Sw12 ∷ CS02 ∷ CCZ013 ∷ Sw12 ∷ Sw01 ∷ CX30 ∷ CCZ012 ∷ CX30 ∷ []) (CCZ123 ∷ CCZ012 ∷ Sw01 ∷ CCZ012 ∷ Sw12 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ CX30 ∷ CCZ012 ∷ CX30 ∷ [])
  b7 = at 8 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00014 ▸
       at 3 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00017 ▸
       at 3 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b8 : Chain (CCZ123 ∷ CCZ012 ∷ Sw01 ∷ CCZ012 ∷ Sw12 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ CX30 ∷ CCZ012 ∷ CX30 ∷ []) (CCZ123 ∷ CCZ012 ∷ Sw01 ∷ CCZ012 ∷ CS23 ∷ Sw12 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw12 ∷ Sw01 ∷ CX30 ∷ CCZ012 ∷ CX30 ∷ [])
  b8 = at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 7 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00003 ▸
       at 4 2 (CS23 ∷ Sw12 ∷ []) wn00020 ▸ done

  b9 : Chain (CCZ123 ∷ CCZ012 ∷ Sw01 ∷ CCZ012 ∷ CS23 ∷ Sw12 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw12 ∷ Sw01 ∷ CX30 ∷ CCZ012 ∷ CX30 ∷ []) (CCZ123 ∷ CCZ012 ∷ Sw01 ∷ CCZ012 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ CX30 ∷ CCZ012 ∷ CX30 ∷ [])
  b9 = at 7 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 5 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS23⁻ ∷ Sw12 ∷ []) wn00021 ▸
       at 9 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 7 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 9 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) wn00022 ▸
       at 10 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸ done

  b10 : Chain (CCZ123 ∷ CCZ012 ∷ Sw01 ∷ CCZ012 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ CX30 ∷ CCZ012 ∷ CX30 ∷ []) (CCZ123 ∷ CCZ012 ∷ Sw01 ∷ CCZ012 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw01 ∷ CX30 ∷ CCZ012 ∷ CX30 ∷ [])
  b10 = at 11 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) wn00023 ▸
       at 8 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 4 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 5 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 6 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 7 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 8 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b11 : Chain (CCZ123 ∷ CCZ012 ∷ Sw01 ∷ CCZ012 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw01 ∷ CX30 ∷ CCZ012 ∷ CX30 ∷ []) (CCZ123 ∷ CCZ012 ∷ Sw01 ∷ CCZ012 ∷ CCZ023 ∷ Sw01 ∷ CX30 ∷ CCZ012 ∷ CX30 ∷ [])
  b11 = at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸
       at 5 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 4 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00014 ▸ done

  b12 : Chain (CCZ123 ∷ CCZ012 ∷ Sw01 ∷ CCZ012 ∷ CCZ023 ∷ Sw01 ∷ CX30 ∷ CCZ012 ∷ CX30 ∷ []) (CCZ123 ∷ CCZ012 ∷ CCZ012 ∷ Sw01 ∷ CCZ023 ∷ Sw01 ∷ CX30 ∷ CCZ012 ∷ CX30 ∷ [])
  b12 = at 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 3 2 (CX10 ∷ Sw01 ∷ []) wn00028 ▸
       at 4 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸
       at 5 2 (CX10 ∷ Sw01 ∷ []) wn00028 ▸
       at 6 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 2 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00011 ▸
       at 2 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸ done

  b13 : Chain (CCZ123 ∷ CCZ012 ∷ CCZ012 ∷ Sw01 ∷ CCZ023 ∷ Sw01 ∷ CX30 ∷ CCZ012 ∷ CX30 ∷ []) (CCZ123 ∷ CCZ012 ∷ CCZ012 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ CX30 ∷ CCZ012 ∷ CX30 ∷ [])
  b13 = at 4 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 5 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 6 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 7 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b14 : Chain (CCZ123 ∷ CCZ012 ∷ CCZ012 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ CX30 ∷ CCZ012 ∷ CX30 ∷ []) (CCZ123 ∷ CCZ012 ∷ CCZ012 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw01 ∷ CS03 ∷ Sw01 ∷ CX30 ∷ CCZ012 ∷ CX30 ∷ [])
  b14 = at 9 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00031 ▸
       at 3 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 4 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 5 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 6 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸ done

  b15 : Chain (CCZ123 ∷ CCZ012 ∷ CCZ012 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw01 ∷ CS03 ∷ Sw01 ∷ CX30 ∷ CCZ012 ∷ CX30 ∷ []) (CCZ123 ∷ CCZ012 ∷ CCZ012 ∷ CCZ123 ∷ CX30 ∷ CCZ012 ∷ CX30 ∷ [])
  b15 = at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸
       at 3 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00031 ▸ done

  b16 : Chain (CCZ123 ∷ CCZ012 ∷ CCZ012 ∷ CCZ123 ∷ CX30 ∷ CCZ012 ∷ CX30 ∷ []) (CX30 ∷ CCZ012 ∷ Sw01 ∷ CX31 ∷ Sw01 ∷ [])
  b16 = at 1 2 [] wn00032 ▸
       at 0 2 [] wn00033 ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 2 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 3 2 (Sw01 ∷ CX21 ∷ []) wn00006 ▸
       at 2 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 3 3 (CX31 ∷ []) (by-assoc Eq.refl) ▸ done

  b17 : Chain (CX30 ∷ CCZ012 ∷ Sw01 ∷ CX31 ∷ Sw01 ∷ []) (CX30 ∷ Sw01 ∷ CCZ012 ∷ CX31 ∷ Sw01 ∷ [])
  b17 = at 1 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 4 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 3 2 (Sw01 ∷ CS02⁻ ∷ []) wn00009 ▸
       at 2 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 1 2 (Sw01 ∷ CS02 ∷ []) wn00010 ▸
       at 2 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00011 ▸
       at 2 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸ done

  b18 : Chain (CX30 ∷ Sw01 ∷ CCZ012 ∷ CX31 ∷ Sw01 ∷ []) (Sw01 ∷ CX31 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw12 ∷ CX32 ∷ Sw12 ∷ Sw01 ∷ [])
  b18 = at 0 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 1 2 (Sw01 ∷ CX21 ∷ []) wn00006 ▸
       at 0 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 1 3 (CX31 ∷ []) (by-assoc Eq.refl) ▸
       at 4 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 3 2 (Sw12 ∷ CX32 ∷ []) wn00013 ▸
       at 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸ done

  b19 : Chain (Sw01 ∷ CX31 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw12 ∷ CX32 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ CX31 ∷ Sw12 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ CX32 ∷ Sw12 ∷ Sw01 ∷ [])
  b19 = at 6 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00014 ▸
       at 5 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 6 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw12 ∷ CS12⁻ ∷ []) wn00015 ▸
       at 3 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw12 ∷ CS12 ∷ []) wn00016 ▸ done

  b20 : Chain (Sw01 ∷ CX31 ∷ Sw12 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ CX32 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ CX02 ∷ Sw12 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ CCZ013 ∷ Sw12 ∷ Sw01 ∷ [])
  b20 = at 3 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00017 ▸
       at 3 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw12 ∷ CX32 ∷ []) wn00013 ▸
       at 2 3 (CCZ012 ∷ CCZ013 ∷ []) (ax cx-ccz) ▸
       at 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (CS12 ∷ Sw12 ∷ []) wn00018 ▸
       at 4 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 2 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸ done

  b21 : Chain (Sw01 ∷ CS12 ∷ CX02 ∷ Sw12 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ CCZ013 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ012 ∷ Sw12 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ [])
  b21 = at 3 2 (CS12⁻ ∷ Sw12 ∷ []) wn00019 ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00014 ▸
       at 1 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00017 ▸
       at 1 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b22 : Chain (Sw01 ∷ CCZ012 ∷ Sw12 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ012 ∷ Sw12 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ [])
  b22 = at 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b23 : Chain (Sw01 ∷ CCZ012 ∷ Sw12 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ012 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw12 ∷ CS03 ∷ Sw12 ∷ Sw01 ∷ [])
  b23 = at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00003 ▸
       at 2 2 (CS23 ∷ Sw12 ∷ []) wn00020 ▸
       at 5 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 3 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS23⁻ ∷ Sw12 ∷ []) wn00021 ▸
       at 7 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 5 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸ done

  b24 : Chain (Sw01 ∷ CCZ012 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw12 ∷ CS03 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ012 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ Sw01 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw12 ∷ Sw12 ∷ Sw01 ∷ [])
  b24 = at 7 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) wn00022 ▸
       at 8 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 9 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) wn00023 ▸
       at 6 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 3 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 4 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸ done

  b25 : Chain (Sw01 ∷ CCZ012 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ Sw01 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw12 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ012 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw12 ∷ Sw12 ∷ Sw01 ∷ [])
  b25 = at 5 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 6 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸ done

  b26 : Chain (Sw01 ∷ CCZ012 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw12 ∷ Sw12 ∷ Sw01 ∷ []) (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ Sw01 ∷ CS02 ∷ CCZ023 ∷ Sw01 ∷ [])
  b26 = at 3 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00014 ▸
       at 1 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 1 2 (CX10 ∷ Sw01 ∷ []) wn00028 ▸
       at 2 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸
       at 3 2 (CX10 ∷ Sw01 ∷ []) wn00028 ▸ done

  b27 : Chain (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ Sw01 ∷ CS02 ∷ CCZ023 ∷ Sw01 ∷ []) (CCZ012 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ [])
  b27 = at 4 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 0 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00011 ▸
       at 0 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 3 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 4 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸ done

  b28 : Chain (CCZ012 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ []) (CCZ012 ∷ CS23 ∷ Sw01 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ [])
  b28 = at 5 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00031 ▸
       at 1 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸ done

  b29 : Chain (CCZ012 ∷ CS23 ∷ Sw01 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ []) (CCZ012 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ [])
  b29 = at 2 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 3 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 4 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b30 : Chain (CCZ012 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ []) (CCZ012 ∷ CCZ123 ∷ [])
  b30 = at 1 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸
       at 1 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00031 ▸ done

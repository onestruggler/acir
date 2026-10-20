{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D013 where

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
open import Examples.Groups.Clifford+CS.Four.Wins.W01 using (wn00001 ; wn00003 ; wn00005 ; wn00006 ; wn00007 ; wn00021 ; wn00024 ; wn00025 ; wn00026 ; wn00027 ; wn00029 ; wn00030 ; wn00031 ; wn00039 ; wn00051 ; wn00074 ; wn00075 ; wn00076 ; wn00081 ; wn00082 ; wn00163 ; wn00166 ; wn00183 ; wn00184)
open import Examples.Groups.Clifford+CS.Four.Wins.W02 using (wn00245 ; wn00261 ; wn00262 ; wn00263 ; wn00264 ; wn00265 ; wn00266 ; wn00267 ; wn00268 ; wn00269 ; wn00270)

-- comm CCZ023 CSd13: 131 steps
lem-comm-CCZ023-CSd13 : ⟪ (CCZ023 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ CCZ023 ∷ []) ⟫ʷ
lem-comm-CCZ023-CSd13 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (run b16))))))))))))))))
  where
  b0 : Chain (CCZ023 ∷ CS13⁻ ∷ []) (CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CS13⁻ ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 0 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 1 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 2 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 3 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CS13⁻ ∷ []) (CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ CS13⁻ ∷ [])
  b1 = at 4 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 4 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00031 ▸
       at 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 5 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸ done

  b2 : Chain (CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ CS13⁻ ∷ []) (Sw01 ∷ CCZ123 ∷ Sw01 ∷ CS13⁻ ∷ [])
  b2 = at 4 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸
       at 2 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 1 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸
       at 0 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 1 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸
       at 1 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (Sw01 ∷ CCZ123 ∷ Sw01 ∷ CS13⁻ ∷ []) (CS02 ∷ CX30 ∷ CS02⁻ ∷ Sw01 ∷ CX31 ∷ CS23 ∷ Sw01 ∷ CS13⁻ ∷ [])
  b3 = at 1 1 (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) wn00075 ▸
       at 0 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 2 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 2 2 (CX20 ∷ Sw01 ∷ []) wn00039 ▸
       at 3 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸ done

  b4 : Chain (CS02 ∷ CX30 ∷ CS02⁻ ∷ Sw01 ∷ CX31 ∷ CS23 ∷ Sw01 ∷ CS13⁻ ∷ []) (CS02 ∷ CX30 ∷ CS02⁻ ∷ CX30 ∷ CS13⁻ ∷ CS23 ∷ [])
  b4 = at 4 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 4 2 (CX20 ∷ Sw01 ∷ []) wn00039 ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 3 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 5 2 [] wn00031 ▸
       at 4 2 (CS13⁻ ∷ CS23 ∷ []) wn00082 ▸ done

  b5 : Chain (CS02 ∷ CX30 ∷ CS02⁻ ∷ CX30 ∷ CS13⁻ ∷ CS23 ∷ []) (CS02 ∷ CX30 ∷ CS02⁻ ∷ CS13⁻ ∷ Sw23 ∷ CX20 ∷ Sw23 ∷ CS23 ∷ [])
  b5 = at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸
       at 3 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 4 2 (CS12⁻ ∷ CX20 ∷ []) wn00261 ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b6 : Chain (CS02 ∷ CX30 ∷ CS02⁻ ∷ CS13⁻ ∷ Sw23 ∷ CX20 ∷ Sw23 ∷ CS23 ∷ []) (CS02 ∷ CX30 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CX30 ∷ CS23 ∷ [])
  b6 = at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b7 : Chain (CS02 ∷ CX30 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CX30 ∷ CS23 ∷ []) (CS02 ∷ CX30 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Sw23 ∷ CX30 ∷ CS23 ∷ [])
  b7 = at 7 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS23⁻ ∷ Sw12 ∷ []) wn00021 ▸
       at 5 2 (CS23⁻ ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) ((CS • CS • CS))) ▸
       at 4 2 (CS13⁻ ∷ Sw12 ∷ []) wn00051 ▸
       at 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸
       at 4 5 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b8 : Chain (CS02 ∷ CX30 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Sw23 ∷ CX30 ∷ CS23 ∷ []) (CS02 ∷ Sw23 ∷ CS12⁻ ∷ CX20 ∷ Sw23 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ [])
  b8 = at 6 2 [] wn00003 ▸
       at 2 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸
       at 1 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸
       at 2 2 (CS12⁻ ∷ CX20 ∷ []) wn00261 ▸ done

  b9 : Chain (CS02 ∷ Sw23 ∷ CS12⁻ ∷ CX20 ∷ Sw23 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ []) (Sw23 ∷ CS03 ∷ CS12⁻ ∷ Sw23 ∷ CX30 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ [])
  b9 = at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸
       at 1 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b10 : Chain (Sw23 ∷ CS03 ∷ CS12⁻ ∷ Sw23 ∷ CX30 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ []) (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CX30 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ [])
  b10 = at 1 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS23⁻ ∷ Sw12 ∷ []) wn00021 ▸
       at 3 2 (CS23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((CS • CS • CS))) ▸
       at 2 2 (CS13⁻ ∷ Sw12 ∷ []) wn00051 ▸
       at 2 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00003 ▸ done

  b11 : Chain (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CX30 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ []) (CS13⁻ ∷ CS02 ∷ CX30 ∷ CS02⁻ ∷ Sw23 ∷ CX20 ∷ Sw01 ∷ Sw23 ∷ CS23 ∷ Sw01 ∷ [])
  b11 = at 2 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸
       at 0 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 5 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 4 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b12 : Chain (CS13⁻ ∷ CS02 ∷ CX30 ∷ CS02⁻ ∷ Sw23 ∷ CX20 ∷ Sw01 ∷ Sw23 ∷ CS23 ∷ Sw01 ∷ []) (CS13⁻ ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ Sw01 ∷ [])
  b12 = at 5 2 (Sw01 ∷ CX21 ∷ []) wn00006 ▸
       at 4 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 5 3 (CX31 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw01 ∷ CS12⁻ ∷ []) wn00076 ▸
       at 2 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 3 2 (Sw01 ∷ CX21 ∷ []) wn00006 ▸
       at 2 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b13 : Chain (CS13⁻ ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ Sw01 ∷ []) (CS13⁻ ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ Sw01 ∷ [])
  b13 = at 3 3 (CX31 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 2 5 (CCZ123 ∷ []) wn00081 ▸
       at 2 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 2 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 3 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 4 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸ done

  b14 : Chain (CS13⁻ ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ Sw01 ∷ []) (CS13⁻ ∷ Sw01 ∷ CS23 ∷ CX12 ∷ Sw01 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ Sw01 ∷ [])
  b14 = at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 2 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 3 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸ done

  b15 : Chain (CS13⁻ ∷ Sw01 ∷ CS23 ∷ CX12 ∷ Sw01 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ Sw01 ∷ []) (CS13⁻ ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ [])
  b15 = at 4 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 5 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸ done

  b16 : Chain (CS13⁻ ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ []) (CS13⁻ ∷ CCZ023 ∷ [])
  b16 = at 2 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00031 ▸ done

-- pass [CS03] [CSd03]: 11 steps
lem-pass-CS03-vs-CSd03 : ⟪ (CS03 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS03-vs-CSd03 = trans (run b0) (run b1)
  where
  b0 : Chain (CS03 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸
       at 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸
       at 1 2 (CS02⁻ ∷ CS02 ∷ []) wn00262 ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 0 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (CS03⁻ ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ []) (CS03⁻ ∷ CS03 ∷ [])
  b1 = at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸ done

-- pass [CS03] [S0 CSd03]: 13 steps
lem-pass-CS03-vs-S0-CSd03 : ⟪ (CS03 ∷ S0 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ CS03⁻ ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS03-vs-S0-CSd03 = trans (run b0) (run b1)
  where
  b0 : Chain (CS03 ∷ S0 ∷ CS03⁻ ∷ []) (S0 ∷ Sw23 ∷ CS02⁻ ∷ CS02 ∷ Sw23 ∷ [])
  b0 = at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸
       at 1 2 (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑))) ▸
       at 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸
       at 1 3 (S0 ∷ CS02⁻ ∷ CS02 ∷ []) wn00263 ▸
       at 0 2 (S0 ∷ Sw23 ∷ []) (sym (low₁-comm (S) ((Swap ↑)))) ▸ done

  b1 : Chain (S0 ∷ Sw23 ∷ CS02⁻ ∷ CS02 ∷ Sw23 ∷ []) (S0 ∷ CS03⁻ ∷ CS03 ∷ [])
  b1 = at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸ done

-- pass [S0] [CS02]: 1 steps
lem-pass-S0-vs-CS02 : ⟪ (S0 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ S0 ∷ []) ⟫ʷ
lem-pass-S0-vs-CS02 = run b0
  where
  b0 : Chain (S0 ∷ CS02 ∷ []) (CS02 ∷ S0 ∷ [])
  b0 = at 0 2 (CS02 ∷ S0 ∷ []) wn00183 ▸ done

-- pass [S0] [CSd02]: 1 steps
lem-pass-S0-vs-CSd02 : ⟪ (S0 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ S0 ∷ []) ⟫ʷ
lem-pass-S0-vs-CSd02 = run b0
  where
  b0 : Chain (S0 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ S0 ∷ [])
  b0 = at 0 2 (CS02⁻ ∷ S0 ∷ []) wn00184 ▸ done

-- comm CCZ023 CS01: 83 steps
lem-comm-CCZ023-CS01 : ⟪ (CCZ023 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CCZ023 ∷ []) ⟫ʷ
lem-comm-CCZ023-CS01 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (run b10))))))))))
  where
  b0 : Chain (CCZ023 ∷ CS01 ∷ []) (CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CS01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 0 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 1 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 2 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 3 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CS01 ∷ []) (CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ CS01 ∷ [])
  b1 = at 4 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 4 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00031 ▸
       at 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 5 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸ done

  b2 : Chain (CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ CS01 ∷ []) (Sw01 ∷ CCZ123 ∷ Sw01 ∷ CS01 ∷ [])
  b2 = at 4 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸
       at 2 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 1 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸
       at 0 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 1 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸
       at 1 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (Sw01 ∷ CCZ123 ∷ Sw01 ∷ CS01 ∷ []) (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ Sw01 ∷ CS01 ∷ [])
  b3 = at 1 1 (CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CS13 ∷ []) wn00163 ▸
       at 0 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 1 2 (CX32 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₁₀)) ▸
       at 2 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸
       at 3 2 (CX32 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₁₀)) ▸
       at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸ done

  b4 : Chain (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ Sw01 ∷ CS01 ∷ []) (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ Sw23 ∷ CS01 ∷ CS02 ∷ Sw23 ∷ [])
  b4 = at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 4 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00031 ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 2 (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap)) ▸
       at 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸
       at 5 2 (CS01 ∷ CS02 ∷ []) wn00245 ▸ done

  b5 : Chain (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ Sw23 ∷ CS01 ∷ CS02 ∷ Sw23 ∷ []) (CS01 ∷ CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ [])
  b5 = at 4 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸
       at 3 2 (CS01 ∷ CX32 ∷ []) (sym (low-comm (CS) (CX₁₀))) ▸
       at 2 2 (CS01 ∷ CS02⁻ ∷ []) wn00264 ▸
       at 1 2 (CS01 ∷ CX32 ∷ []) (sym (low-comm (CS) (CX₁₀))) ▸
       at 0 2 (CS01 ∷ CS02 ∷ []) wn00245 ▸ done

  b6 : Chain (CS01 ∷ CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ []) (CS01 ∷ CS02 ∷ CX32 ∷ Sw01 ∷ CS12⁻ ∷ CX32 ∷ CS13 ∷ Sw01 ∷ [])
  b6 = at 6 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 6 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 5 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw01 ∷ CX32 ∷ []) (sym (low-comm (Swap) (CX₁₀))) ▸
       at 3 2 (Sw01 ∷ CS12⁻ ∷ []) wn00076 ▸ done

  b7 : Chain (CS01 ∷ CS02 ∷ CX32 ∷ Sw01 ∷ CS12⁻ ∷ CX32 ∷ CS13 ∷ Sw01 ∷ []) (CS01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ Sw01 ∷ [])
  b7 = at 2 2 (Sw01 ∷ CX32 ∷ []) (sym (low-comm (Swap) (CX₁₀))) ▸
       at 1 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 2 5 (CCZ123 ∷ []) wn00166 ▸
       at 2 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 2 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 3 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 4 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸ done

  b8 : Chain (CS01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ Sw01 ∷ []) (CS01 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ Sw01 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ Sw01 ∷ [])
  b8 = at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 2 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 3 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸ done

  b9 : Chain (CS01 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ Sw01 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ Sw01 ∷ []) (CS01 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ [])
  b9 = at 4 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 5 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸ done

  b10 : Chain (CS01 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ []) (CS01 ∷ CCZ023 ∷ [])
  b10 = at 2 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00031 ▸ done

-- pass [CS23] [CS01]: 1 steps
lem-pass-CS23-vs-CS01 : ⟪ (CS23 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CS23 ∷ []) ⟫ʷ
lem-pass-CS23-vs-CS01 = run b0
  where
  b0 : Chain (CS23 ∷ CS01 ∷ []) (CS01 ∷ CS23 ∷ [])
  b0 = at 0 2 (CS01 ∷ CS23 ∷ []) (sym (low-comm (CS) (CS))) ▸ done

-- pass [S0] [CS01]: 1 steps
lem-pass-S0-vs-CS01 : ⟪ (S0 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ S0 ∷ []) ⟫ʷ
lem-pass-S0-vs-CS01 = run b0
  where
  b0 : Chain (S0 ∷ CS01 ∷ []) (CS01 ∷ S0 ∷ [])
  b0 = at 0 2 (CS01 ∷ S0 ∷ []) wn00265 ▸ done

-- pass [CCZ023] [CS23]: 51 steps
lem-pass-CCZ023-vs-CS23 : ⟪ (CCZ023 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CCZ023 ∷ []) ⟫ʷ
lem-pass-CCZ023-vs-CS23 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (run b6))))))
  where
  b0 : Chain (CCZ023 ∷ CS23 ∷ []) (CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ Sw01 ∷ [])
  b0 = at 2 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 1 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 0 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 1 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 2 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 3 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸ done

  b1 : Chain (CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ Sw01 ∷ []) (CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ CS23 ∷ Sw01 ∷ [])
  b1 = at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 4 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00031 ▸
       at 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b2 : Chain (CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ CS23 ∷ Sw01 ∷ []) (Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CS23 ∷ Sw01 ∷ [])
  b2 = at 5 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 4 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸
       at 2 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 1 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸
       at 0 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 1 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸ done

  b3 : Chain (Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CS23 ∷ Sw01 ∷ []) (CS23 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ Sw01 ∷ [])
  b3 = at 1 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (CS23 ∷ CCZ123 ∷ []) wn00266 ▸
       at 0 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 2 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 2 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 3 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 4 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸ done

  b4 : Chain (CS23 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ Sw01 ∷ []) (CS23 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ Sw01 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ Sw01 ∷ [])
  b4 = at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 2 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 3 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸ done

  b5 : Chain (CS23 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ Sw01 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ Sw01 ∷ []) (CS23 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ [])
  b5 = at 4 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 5 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸ done

  b6 : Chain (CS23 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ []) (CS23 ∷ CCZ023 ∷ [])
  b6 = at 2 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00031 ▸ done

-- pass [CCZ023] [CZ23]: 51 steps
lem-pass-CCZ023-vs-CZ23 : ⟪ (CCZ023 ∷ CZ23 ∷ []) ⟫ʷ ≈ ⟪ (CZ23 ∷ CCZ023 ∷ []) ⟫ʷ
lem-pass-CCZ023-vs-CZ23 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (run b6))))))
  where
  b0 : Chain (CCZ023 ∷ CZ23 ∷ []) (CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ CZ23 ∷ Sw01 ∷ [])
  b0 = at 2 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 1 2 (Sw01 ∷ CZ23 ∷ []) (sym (low-comm (Swap) (CZ))) ▸
       at 0 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 1 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 2 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 3 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸ done

  b1 : Chain (CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ CZ23 ∷ Sw01 ∷ []) (CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ CZ23 ∷ Sw01 ∷ [])
  b1 = at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 4 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00031 ▸
       at 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b2 : Chain (CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ CZ23 ∷ Sw01 ∷ []) (Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CZ23 ∷ Sw01 ∷ [])
  b2 = at 5 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 4 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸
       at 2 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 1 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸
       at 0 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 1 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸ done

  b3 : Chain (Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CZ23 ∷ Sw01 ∷ []) (CZ23 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ Sw01 ∷ [])
  b3 = at 1 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (CZ23 ∷ CCZ123 ∷ []) wn00267 ▸
       at 0 2 (CZ23 ∷ Sw01 ∷ []) (low-comm (Swap) (CZ)) ▸
       at 2 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 2 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 3 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 4 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸ done

  b4 : Chain (CZ23 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ Sw01 ∷ []) (CZ23 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ Sw01 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ Sw01 ∷ [])
  b4 = at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 2 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 3 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸ done

  b5 : Chain (CZ23 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ Sw01 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ Sw01 ∷ []) (CZ23 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ [])
  b5 = at 4 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 5 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸ done

  b6 : Chain (CZ23 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ []) (CZ23 ∷ CCZ023 ∷ [])
  b6 = at 2 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00031 ▸ done

-- pass [S0] [CSd01]: 1 steps
lem-pass-S0-vs-CSd01 : ⟪ (S0 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ S0 ∷ []) ⟫ʷ
lem-pass-S0-vs-CSd01 = run b0
  where
  b0 : Chain (S0 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ S0 ∷ [])
  b0 = at 0 2 (CS01⁻ ∷ S0 ∷ []) wn00268 ▸ done

-- pass [CSd23] [CS01]: 1 steps
lem-pass-CSd23-vs-CS01 : ⟪ (CS23⁻ ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CS23⁻ ∷ []) ⟫ʷ
lem-pass-CSd23-vs-CS01 = run b0
  where
  b0 : Chain (CS23⁻ ∷ CS01 ∷ []) (CS01 ∷ CS23⁻ ∷ [])
  b0 = at 0 2 (CS01 ∷ CS23⁻ ∷ []) (sym (low-comm (CS) ((CS • CS • CS)))) ▸ done

-- pass [CSd03] [CS01]: 9 steps
lem-pass-CSd03-vs-CS01 : ⟪ (CS03⁻ ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-CSd03-vs-CS01 = trans (run b0) (run b1)
  where
  b0 : Chain (CS03⁻ ∷ CS01 ∷ []) (CS01 ∷ CS03⁻ ∷ Sw23 ∷ Sw23 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 2 (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap)) ▸
       at 0 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸
       at 1 2 (CS01 ∷ CS02⁻ ∷ []) wn00264 ▸
       at 0 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (CS01 ∷ CS03⁻ ∷ Sw23 ∷ Sw23 ∷ []) (CS01 ∷ CS03⁻ ∷ [])
  b1 = at 2 2 [] wn00003 ▸ done

-- pass [CCZ023] [CSd23]: 51 steps
lem-pass-CCZ023-vs-CSd23 : ⟪ (CCZ023 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ CCZ023 ∷ []) ⟫ʷ
lem-pass-CCZ023-vs-CSd23 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (run b6))))))
  where
  b0 : Chain (CCZ023 ∷ CS23⁻ ∷ []) (CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ CS23⁻ ∷ Sw01 ∷ [])
  b0 = at 2 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 1 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 0 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 1 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 2 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 3 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸ done

  b1 : Chain (CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ CS23⁻ ∷ Sw01 ∷ []) (CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ CS23⁻ ∷ Sw01 ∷ [])
  b1 = at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 4 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00031 ▸
       at 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b2 : Chain (CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ CS23⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CS23⁻ ∷ Sw01 ∷ [])
  b2 = at 5 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 4 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸
       at 2 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 1 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸
       at 0 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 1 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸ done

  b3 : Chain (Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CS23⁻ ∷ Sw01 ∷ []) (CS23⁻ ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ Sw01 ∷ [])
  b3 = at 1 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (CS23⁻ ∷ CCZ123 ∷ []) wn00269 ▸
       at 0 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 2 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 2 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 3 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 4 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸ done

  b4 : Chain (CS23⁻ ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ Sw01 ∷ []) (CS23⁻ ∷ Sw01 ∷ CS23 ∷ CX12 ∷ Sw01 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ Sw01 ∷ [])
  b4 = at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 2 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 3 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸ done

  b5 : Chain (CS23⁻ ∷ Sw01 ∷ CS23 ∷ CX12 ∷ Sw01 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ Sw01 ∷ []) (CS23⁻ ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ [])
  b5 = at 4 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 5 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸ done

  b6 : Chain (CS23⁻ ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ []) (CS23⁻ ∷ CCZ023 ∷ [])
  b6 = at 2 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00031 ▸ done

-- pass [CSd03] [CSd01]: 9 steps
lem-pass-CSd03-vs-CSd01 : ⟪ (CS03⁻ ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-CSd03-vs-CSd01 = trans (run b0) (run b1)
  where
  b0 : Chain (CS03⁻ ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CS03⁻ ∷ Sw23 ∷ Sw23 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 2 (Sw23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (Swap)) ▸
       at 0 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸
       at 1 2 (CS01⁻ ∷ CS02⁻ ∷ []) wn00270 ▸
       at 0 2 (CS01⁻ ∷ Sw23 ∷ []) (sym (low-comm ((CS • CS • CS)) (Swap))) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (CS01⁻ ∷ CS03⁻ ∷ Sw23 ∷ Sw23 ∷ []) (CS01⁻ ∷ CS03⁻ ∷ [])
  b1 = at 2 2 [] wn00003 ▸ done

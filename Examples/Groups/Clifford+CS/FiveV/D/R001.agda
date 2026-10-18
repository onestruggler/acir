{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.FiveV.D.R001 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.FiveV.WinSig using (WsL ; wl0001 ; wl0002 ; wl0003 ; wl0004 ; wl0005 ; wl0006 ; wl0007 ; wl0008 ; wl0009 ; wl0010 ; wl0011 ; wl0012 ; wl0013 ; wl0014 ; wl0015 ; wl0016 ; wl0017 ; wl0018 ; wl0019 ; wl0020 ; wl0021 ; wl0022 ; wl0023 ; wl0024 ; wl0025 ; wl0026 ; wl0027 ; wl0028 ; wl0029 ; wl0030 ; wl0031 ; wl0032 ; wl0033 ; wl0034 ; wl0035 ; wl0036 ; wl0037 ; wl0038 ; wl0039 ; wl0040 ; wl0041 ; wl0042 ; wl0043 ; wl0044 ; wl0045 ; wl0046 ; wl0047 ; wl0048 ; wl0049 ; wl0050 ; wl0051)
open import Examples.Groups.Clifford+CS.FiveV.Chain

-- comm push CS04 sw1 R: 5 steps
lem-comm-push-CS04-sw1-R : WsL → ⟪ (Sw12 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-CS04-sw1-R c4 = run b0
  where
  b0 : Chain (Sw12 ∷ CS04 ∷ []) (CS04 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 1 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 2 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 0 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm push CS04 sw2 R: 7 steps
lem-comm-push-CS04-sw2-R : WsL → ⟪ (Sw23 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-CS04-sw2-R c4 = run b0
  where
  b0 : Chain (Sw23 ∷ CS04 ∷ []) (CS04 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0002 c4) ▸
       at 2 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 3 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 4 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 5 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (sym (wl0002 c4)) ▸
       at 0 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm push CS04 sw1 L: 5 steps
lem-comm-push-CS04-sw1-L : WsL → ⟪ (CS04 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CS04 ∷ []) ⟫ʷ
lem-comm-push-CS04-sw1-L c4 = run b0
  where
  b0 : Chain (CS04 ∷ Sw12 ∷ []) (Sw12 ∷ CS04 ∷ [])
  b0 = at 0 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 1 2 (Sw12 ∷ CS03 ∷ []) (wl0001 c4) ▸
       at 0 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 1 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm push CCZ034 sw1 L: 83 steps
lem-comm-push-CCZ034-sw1-L : WsL → ⟪ (CCZ034 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CCZ034 ∷ []) ⟫ʷ
lem-comm-push-CCZ034-sw1-L c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (run b10))))))))))
  where
  b0 : Chain (CCZ034 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ [])
  b0 = at 0 1 (Sw23 ∷ CCZ024 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw12 ∷ CCZ014 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ CCZ013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ CS14 ∷ Sw34 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ [])
  b1 = at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0003 c4) ▸
       at 4 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw23 ∷ Sw12 ∷ CS14 ∷ Sw34 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw23 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ [])
  b2 = at 3 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 4 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0004 c4) ▸
       at 1 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0005 c4)) ▸ done

  b3 : Chain (Sw23 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (CS34 ∷ Sw23 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ Sw23 ∷ Sw12 ∷ [])
  b3 = at 4 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 2 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS24⁻ ∷ Sw12 ∷ []) (sym (wl0007 c4)) ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R c4) ▸
       at 6 2 [] (wl0006 c4) ▸
       at 0 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0008 c4)) ▸ done

  b4 : Chain (CS34 ∷ Sw23 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ Sw23 ∷ Sw12 ∷ []) (CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw12 ∷ CS04 ∷ [])
  b4 = at 3 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0009 c4)) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 3 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS04 ∷ Sw23 ∷ []) (lem-comm-push-CS04-sw2-R c4) ▸
       at 5 2 [] (wl0003 c4) ▸
       at 4 2 (Sw12 ∷ CS04 ∷ []) (lem-comm-push-CS04-sw1-L c4) ▸ done

  b5 : Chain (CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw12 ∷ CS04 ∷ []) (Sw12 ∷ Sw23 ∷ CS24 ∷ CX02 ∷ Sw23 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ [])
  b5 = at 3 2 (Sw12 ∷ CX03 ∷ []) (wl0010 c4) ▸
       at 2 2 (Sw12 ∷ CS34⁻ ∷ []) (sym (c₃ (Swap ↑) (CS • CS • CS))) ▸
       at 1 2 (Sw12 ∷ CX03 ∷ []) (wl0010 c4) ▸
       at 0 2 (Sw12 ∷ CS34 ∷ []) (sym (c₃ (Swap ↑) (CS))) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 2 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0011 c4)) ▸
       at 4 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0003 c4) ▸ done

  b6 : Chain (Sw12 ∷ Sw23 ∷ CS24 ∷ CX02 ∷ Sw23 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ CS14 ∷ CX01 ∷ Sw12 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ Sw23 ∷ [])
  b6 = at 4 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0012 c4)) ▸
       at 6 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0003 c4) ▸
       at 6 2 (CS04 ∷ Sw23 ∷ []) (lem-comm-push-CS04-sw2-R c4) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 3 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 c4)) ▸
       at 5 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0006 c4) ▸ done

  b7 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ CS14 ∷ CX01 ∷ Sw12 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ Sw23 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ Sw34 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw12 ∷ Sw23 ∷ [])
  b7 = at 5 2 (CS14⁻ ∷ Sw12 ∷ []) (sym (wl0014 c4)) ▸
       at 7 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0006 c4) ▸
       at 7 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R c4) ▸
       at 3 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 5 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0004 c4) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸ done

  b8 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ Sw34 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw12 ∷ Sw23 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b8 = at 7 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0004 c4) ▸
       at 7 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 9 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0004 c4) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0003 c4) ▸ done

  b9 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ CCZ013 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b9 = at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0003 c4) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (wl0003 c4) ▸
       at 5 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 4 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸ done

  b10 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ CCZ013 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Sw12 ∷ CCZ034 ∷ [])
  b10 = at 3 3 (CCZ014 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (CCZ024 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (CCZ034 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm push CS04 sw0 L: 5 steps
lem-comm-push-CS04-sw0-L : WsL → ⟪ (CS04 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CS14 ∷ []) ⟫ʷ
lem-comm-push-CS04-sw0-L c4 = run b0
  where
  b0 : Chain (CS04 ∷ Sw01 ∷ []) (Sw01 ∷ CS14 ∷ [])
  b0 = at 0 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 1 2 (Sw01 ∷ CS13 ∷ []) (wl0015 c4) ▸
       at 0 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 1 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm push CCZ034 sw0 L: 64 steps
lem-comm-push-CCZ034-sw0-L : WsL → ⟪ (CCZ034 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CCZ134 ∷ []) ⟫ʷ
lem-comm-push-CCZ034-sw0-L c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (CCZ034 ∷ Sw01 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ [])
  b0 = at 0 1 (Sw23 ∷ CCZ024 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw12 ∷ CCZ014 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ CCZ013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ []) (Sw23 ∷ Sw12 ∷ CS14 ∷ Sw34 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ [])
  b1 = at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0003 c4) ▸
       at 4 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw23 ∷ Sw12 ∷ CS14 ∷ Sw34 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ []) (Sw23 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ [])
  b2 = at 3 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 4 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0004 c4) ▸
       at 1 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0005 c4)) ▸ done

  b3 : Chain (Sw23 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ []) (CS34 ∷ Sw23 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ Sw23 ∷ Sw01 ∷ [])
  b3 = at 4 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 2 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS24⁻ ∷ Sw12 ∷ []) (sym (wl0007 c4)) ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R c4) ▸
       at 6 2 [] (wl0006 c4) ▸
       at 0 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0008 c4)) ▸ done

  b4 : Chain (CS34 ∷ Sw23 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ Sw23 ∷ Sw01 ∷ []) (CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw01 ∷ CS14 ∷ [])
  b4 = at 3 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0009 c4)) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 3 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS04 ∷ Sw23 ∷ []) (lem-comm-push-CS04-sw2-R c4) ▸
       at 5 2 [] (wl0003 c4) ▸
       at 4 2 (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L c4) ▸ done

  b5 : Chain (CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw01 ∷ CS14 ∷ []) (Sw01 ∷ Sw23 ∷ CS24 ∷ CX12 ∷ Sw23 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ [])
  b5 = at 3 2 (Sw01 ∷ CX13 ∷ []) (wl0016 c4) ▸
       at 2 2 (Sw01 ∷ CS34⁻ ∷ []) (sym (c₂ (Swap) ((CS • CS • CS) ↑))) ▸
       at 1 2 (Sw01 ∷ CX13 ∷ []) (wl0016 c4) ▸
       at 0 2 (Sw01 ∷ CS34 ∷ []) (sym (c₂ (Swap) (CS ↑))) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 2 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0011 c4)) ▸
       at 4 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0003 c4) ▸ done

  b6 : Chain (Sw01 ∷ Sw23 ∷ CS24 ∷ CX12 ∷ Sw23 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) (Sw01 ∷ Sw23 ∷ Sw34 ∷ CS23 ∷ CX12 ∷ Sw34 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Sw23 ∷ [])
  b6 = at 4 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0012 c4)) ▸
       at 6 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0003 c4) ▸
       at 6 2 (CS14 ∷ Sw23 ∷ []) (sym (wl0017 c4)) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 4 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0004 c4) ▸
       at 4 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸ done

  b7 : Chain (Sw01 ∷ Sw23 ∷ Sw34 ∷ CS23 ∷ CX12 ∷ Sw34 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Sw23 ∷ []) (Sw01 ∷ CCZ134 ∷ [])
  b7 = at 6 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0004 c4) ▸
       at 6 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 8 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0004 c4) ▸
       at 3 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (CCZ124 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CCZ034 at 2: 4 steps
lem-resp-CCZ034-at-2 : WsL → ⟪ (CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CCZ134 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CCZ034-at-2 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ []) (Sw12 ∷ Sw01 ∷ CCZ134 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 0 2 (Sw12 ∷ CCZ034 ∷ []) (lem-comm-push-CCZ034-sw1-L c4) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 1 2 (Sw01 ∷ CCZ134 ∷ []) (lem-comm-push-CCZ034-sw0-L c4) ▸ done


-- comm CX12 CCZ034: 15 steps
lem-comm-CX12-CCZ034 : WsL → ⟪ (CX12 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CX12 ∷ []) ⟫ʷ
lem-comm-CX12-CCZ034 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX12 ∷ CCZ034 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ CX34 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw12 ∷ CX23 ∷ []) (wl0019 c4) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (CX24 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw23 ∷ CX34 ∷ []) (wl0020 c4) ▸
       at 4 2 (CCZ012 ∷ CX34 ∷ []) (sym (c₃ (CCZ) (CX₀₁))) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ CX34 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (CCZ034 ∷ CX12 ∷ [])
  b1 = at 5 2 (Sw23 ∷ CX24 ∷ []) (wl0021 c4) ▸
       at 6 1 (Sw34 ∷ CX23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0004 c4) ▸
       at 7 2 (Sw12 ∷ CX13 ∷ []) (wl0022 c4) ▸
       at 8 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (wl0003 c4) ▸
       at 0 9 (CCZ034 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CSd02 at 1: 2 steps
lem-resp-CSd02-at-1 : WsL → ⟪ (CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CS12⁻ ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CSd02-at-1 c4 = run b0
  where
  b0 : Chain (CS02⁻ ∷ []) (Sw01 ∷ CS12⁻ ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 0 2 (Sw01 ∷ CS12⁻ ∷ []) (wl0023 c4) ▸ done


-- resp CCZ034 at 1: 2 steps
lem-resp-CCZ034-at-1 : WsL → ⟪ (CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CCZ134 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CCZ034-at-1 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ []) (Sw01 ∷ CCZ134 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 0 2 (Sw01 ∷ CCZ134 ∷ []) (lem-comm-push-CCZ034-sw0-L c4) ▸ done


-- resp CS02 at 1: 2 steps
lem-resp-CS02-at-1 : WsL → ⟪ (CS02 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CS12 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CS02-at-1 c4 = run b0
  where
  b0 : Chain (CS02 ∷ []) (Sw01 ∷ CS12 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 0 2 (Sw01 ∷ CS12 ∷ []) (wl0024 c4) ▸ done


-- comm push TOFF034 sw0 L: 86 steps
lem-comm-push-TOFF034-sw0-L : WsL → ⟪ (Toff034 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Toff134 ∷ []) ⟫ʷ
lem-comm-push-TOFF034-sw0-L c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (run b10))))))))))
  where
  b0 : Chain (Toff034 ∷ Sw01 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Toff024 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw12 ∷ Toff014 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ [])
  b1 = at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 10 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸ done

  b2 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ []) (Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ [])
  b2 = at 11 2 [] (wl0003 c4) ▸
       at 2 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 5 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸ done

  b3 : Chain (Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ []) (Sw23 ∷ K0 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ [])
  b3 = at 9 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 7 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 9 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 10 2 [] (wl0004 c4) ▸
       at 1 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 2 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0005 c4)) ▸
       at 5 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸ done

  b4 : Chain (Sw23 ∷ K0 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ []) (Sw23 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw01 ∷ [])
  b4 = at 3 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS24⁻ ∷ Sw12 ∷ []) (sym (wl0007 c4)) ▸
       at 7 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 5 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R c4) ▸
       at 7 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 8 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 9 2 [] (wl0006 c4) ▸ done

  b5 : Chain (Sw23 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw01 ∷ []) (K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw01 ∷ [])
  b5 = at 0 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 1 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0008 c4)) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 2 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0009 c4)) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS04 ∷ Sw23 ∷ []) (lem-comm-push-CS04-sw2-R c4) ▸ done

  b6 : Chain (K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw01 ∷ []) (K0 ∷ CS34 ∷ CX03 ∷ Sw01 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1 ∷ ι ∷ [])
  b6 = at 6 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 7 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 8 2 [] (wl0003 c4) ▸
       at 7 2 (Sw01 ∷ ι ∷ []) (sym (wl0025 c4)) ▸
       at 6 2 (Sw01 ∷ K1 ∷ []) (wl0026 c4) ▸
       at 5 2 (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L c4) ▸
       at 4 2 (Sw01 ∷ CX13 ∷ []) (wl0016 c4) ▸
       at 3 2 (Sw01 ∷ CS34⁻ ∷ []) (sym (c₂ (Swap) ((CS • CS • CS) ↑))) ▸ done

  b7 : Chain (K0 ∷ CS34 ∷ CX03 ∷ Sw01 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1 ∷ ι ∷ []) (Sw01 ∷ Sw23 ∷ K1 ∷ CS24 ∷ CX12 ∷ Sw23 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1 ∷ ι ∷ [])
  b7 = at 2 2 (Sw01 ∷ CX13 ∷ []) (wl0016 c4) ▸
       at 1 2 (Sw01 ∷ CS34 ∷ []) (sym (c₂ (Swap) (CS ↑))) ▸
       at 0 2 (Sw01 ∷ K1 ∷ []) (wl0026 c4) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 2 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 3 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0011 c4)) ▸
       at 5 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0003 c4) ▸ done

  b8 : Chain (Sw01 ∷ Sw23 ∷ K1 ∷ CS24 ∷ CX12 ∷ Sw23 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1 ∷ ι ∷ []) (Sw01 ∷ Sw23 ∷ Sw34 ∷ K1 ∷ Sw34 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K1 ∷ ι ∷ Sw23 ∷ [])
  b8 = at 5 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0012 c4)) ▸
       at 7 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0003 c4) ▸
       at 7 2 (CS14 ∷ Sw23 ∷ []) (sym (wl0017 c4)) ▸
       at 8 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸ done

  b9 : Chain (Sw01 ∷ Sw23 ∷ Sw34 ∷ K1 ∷ Sw34 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K1 ∷ ι ∷ Sw23 ∷ []) (Sw01 ∷ Sw23 ∷ Sw34 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw34 ∷ K1 ∷ ι ∷ Sw23 ∷ [])
  b9 = at 5 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0004 c4) ▸
       at 5 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 7 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0004 c4) ▸
       at 7 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 9 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0004 c4) ▸ done

  b10 : Chain (Sw01 ∷ Sw23 ∷ Sw34 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw34 ∷ K1 ∷ ι ∷ Sw23 ∷ []) (Sw01 ∷ Toff134 ∷ [])
  b10 = at 9 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 10 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 3 8 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (wl0027 c4) ▸
       at 3 8 (Toff123 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff124 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff134 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp TOFF034 at 1: 2 steps
lem-resp-TOFF034-at-1 : WsL → ⟪ (Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Toff134 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-TOFF034-at-1 c4 = run b0
  where
  b0 : Chain (Toff034 ∷ []) (Sw01 ∷ Toff134 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 0 2 (Sw01 ∷ Toff134 ∷ []) (lem-comm-push-TOFF034-sw0-L c4) ▸ done


-- comm CSd12 TOFF034: 15 steps
lem-comm-CSd12-TOFF034 : WsL → ⟪ (CS12⁻ ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CS12⁻ ∷ []) ⟫ʷ
lem-comm-CSd12-TOFF034 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS12⁻ ∷ Toff034 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ CS34⁻ ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw12 ∷ CS23⁻ ∷ []) (wl0028 c4) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw23 ∷ CS34⁻ ∷ []) (wl0012 c4) ▸
       at 4 2 (Toff012 ∷ CS34⁻ ∷ []) (sym (c₃ (Toff) (CS • CS • CS))) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ CS34⁻ ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Toff034 ∷ CS12⁻ ∷ [])
  b1 = at 5 2 (Sw23 ∷ CS24⁻ ∷ []) (wl0009 c4) ▸
       at 6 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0004 c4) ▸
       at 7 2 (Sw12 ∷ CS13⁻ ∷ []) (wl0029 c4) ▸
       at 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (wl0003 c4) ▸
       at 0 9 (Toff034 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CCZ013 at 2: 5 steps
lem-resp-CCZ013-at-2 : WsL → ⟪ (CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CCZ013-at-2 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ []) (Sw12 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 1 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 1 2 (Sw01 ∷ CCZ123 ∷ []) (wl0030 c4) ▸ done


-- resp TOFF103 at 2: 5 steps
lem-resp-TOFF103-at-2 : WsL → ⟪ (Toff103 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ Toff213 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-TOFF103-at-2 c4 = run b0
  where
  b0 : Chain (Toff103 ∷ []) (Sw12 ∷ Sw01 ∷ Toff213 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 1 3 (Toff203 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 1 2 (Sw01 ∷ Toff213 ∷ []) (sym (wl0031 c4)) ▸ done


-- resp CZ14 at 2: 4 steps
lem-resp-CZ14-at-2 : WsL → ⟪ (CZ14 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CZ24 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CZ14-at-2 c4 = run b0
  where
  b0 : Chain (CZ14 ∷ []) (Sw12 ∷ Sw01 ∷ CZ24 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 0 2 (Sw12 ∷ CZ24 ∷ []) (wl0032 c4) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 1 2 (Sw01 ∷ CZ24 ∷ []) (sym (c₂ (Swap) (Swap ↑ • CZ • Swap ↑))) ▸ done


-- comm CZ12 CCZ034: 15 steps
lem-comm-CZ12-CCZ034 : WsL → ⟪ (CZ12 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CZ12 ∷ []) ⟫ʷ
lem-comm-CZ12-CCZ034 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CZ12 ∷ CCZ034 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ CZ34 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw12 ∷ CZ23 ∷ []) (wl0033 c4) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (CZ24 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw23 ∷ CZ34 ∷ []) (wl0034 c4) ▸
       at 4 2 (CCZ012 ∷ CZ34 ∷ []) (sym (c₃ (CCZ) (CZ))) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ CZ34 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (CCZ034 ∷ CZ12 ∷ [])
  b1 = at 5 2 (Sw23 ∷ CZ24 ∷ []) (wl0035 c4) ▸
       at 6 1 (Sw34 ∷ CZ23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0004 c4) ▸
       at 7 2 (Sw12 ∷ CZ13 ∷ []) (wl0036 c4) ▸
       at 8 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (wl0003 c4) ▸
       at 0 9 (CCZ034 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CZ12 TOFF034: 15 steps
lem-comm-CZ12-TOFF034 : WsL → ⟪ (CZ12 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CZ12 ∷ []) ⟫ʷ
lem-comm-CZ12-TOFF034 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CZ12 ∷ Toff034 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ CZ34 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw12 ∷ CZ23 ∷ []) (wl0033 c4) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (CZ24 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw23 ∷ CZ34 ∷ []) (wl0034 c4) ▸
       at 4 2 (Toff012 ∷ CZ34 ∷ []) (sym (c₃ (Toff) (CZ))) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ CZ34 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Toff034 ∷ CZ12 ∷ [])
  b1 = at 5 2 (Sw23 ∷ CZ24 ∷ []) (wl0035 c4) ▸
       at 6 1 (Sw34 ∷ CZ23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0004 c4) ▸
       at 7 2 (Sw12 ∷ CZ13 ∷ []) (wl0036 c4) ▸
       at 8 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (wl0003 c4) ▸
       at 0 9 (Toff034 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm push TOFF034 sw1 L: 110 steps
lem-comm-push-TOFF034-sw1-L : WsL → ⟪ (Toff034 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Toff034 ∷ []) ⟫ʷ
lem-comm-push-TOFF034-sw1-L c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (run b13)))))))))))))
  where
  b0 : Chain (Toff034 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Toff024 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw12 ∷ Toff014 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ [])
  b1 = at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 10 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸ done

  b2 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ [])
  b2 = at 11 2 [] (wl0003 c4) ▸
       at 2 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 5 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸ done

  b3 : Chain (Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw23 ∷ K0 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ [])
  b3 = at 9 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 7 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 9 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 10 2 [] (wl0004 c4) ▸
       at 1 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 2 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0005 c4)) ▸
       at 5 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸ done

  b4 : Chain (Sw23 ∷ K0 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw23 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw12 ∷ [])
  b4 = at 3 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS24⁻ ∷ Sw12 ∷ []) (sym (wl0007 c4)) ▸
       at 7 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 5 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R c4) ▸
       at 7 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 8 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 9 2 [] (wl0006 c4) ▸ done

  b5 : Chain (Sw23 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw12 ∷ []) (K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw12 ∷ [])
  b5 = at 0 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 1 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0008 c4)) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 2 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0009 c4)) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS04 ∷ Sw23 ∷ []) (lem-comm-push-CS04-sw2-R c4) ▸ done

  b6 : Chain (K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw12 ∷ []) (K0 ∷ CS34 ∷ CX03 ∷ Sw12 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K0 ∷ ι ∷ [])
  b6 = at 6 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 7 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 8 2 [] (wl0003 c4) ▸
       at 7 2 (Sw12 ∷ ι ∷ []) (c₁ (iI) (Swap)) ▸
       at 6 2 (Sw12 ∷ K0 ∷ []) (c₁ (K) (Swap)) ▸
       at 5 2 (Sw12 ∷ CS04 ∷ []) (lem-comm-push-CS04-sw1-L c4) ▸
       at 4 2 (Sw12 ∷ CX03 ∷ []) (wl0010 c4) ▸
       at 3 2 (Sw12 ∷ CS34⁻ ∷ []) (sym (c₃ (Swap ↑) (CS • CS • CS))) ▸ done

  b7 : Chain (K0 ∷ CS34 ∷ CX03 ∷ Sw12 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K0 ∷ ι ∷ []) (Sw12 ∷ Sw23 ∷ K0 ∷ CS24 ∷ CX02 ∷ Sw23 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K0 ∷ ι ∷ [])
  b7 = at 2 2 (Sw12 ∷ CX03 ∷ []) (wl0010 c4) ▸
       at 1 2 (Sw12 ∷ CS34 ∷ []) (sym (c₃ (Swap ↑) (CS))) ▸
       at 0 2 (Sw12 ∷ K0 ∷ []) (c₁ (K) (Swap)) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 2 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 3 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0011 c4)) ▸
       at 5 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0003 c4) ▸ done

  b8 : Chain (Sw12 ∷ Sw23 ∷ K0 ∷ CS24 ∷ CX02 ∷ Sw23 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K0 ∷ ι ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ K0 ∷ Sw12 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0 ∷ ι ∷ Sw23 ∷ [])
  b8 = at 5 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0012 c4)) ▸
       at 7 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0003 c4) ▸
       at 7 2 (CS04 ∷ Sw23 ∷ []) (lem-comm-push-CS04-sw2-R c4) ▸
       at 8 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 3 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸ done

  b9 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ K0 ∷ Sw12 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0 ∷ ι ∷ Sw23 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ Sw12 ∷ ι ∷ Sw23 ∷ [])
  b9 = at 4 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 c4)) ▸
       at 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0006 c4) ▸
       at 6 2 (CS14⁻ ∷ Sw12 ∷ []) (sym (wl0014 c4)) ▸
       at 8 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0006 c4) ▸
       at 8 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R c4) ▸
       at 9 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸ done

  b10 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ Sw12 ∷ ι ∷ Sw23 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw34 ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ [])
  b10 = at 10 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 3 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 4 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 6 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0004 c4) ▸
       at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0004 c4) ▸ done

  b11 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw34 ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b11 = at 8 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 10 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (wl0004 c4) ▸
       at 10 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 11 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 5 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b12 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ Sw23 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b12 = at 6 2 [] (wl0003 c4) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0003 c4) ▸
       at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (wl0003 c4) ▸
       at 11 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸ done

  b13 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ Sw23 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Sw12 ∷ Toff034 ∷ [])
  b13 = at 12 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 5 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 4 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (Toff014 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff024 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff034 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp TOFF034 at 2: 4 steps
lem-resp-TOFF034-at-2 : WsL → ⟪ (Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ Toff134 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-TOFF034-at-2 c4 = run b0
  where
  b0 : Chain (Toff034 ∷ []) (Sw12 ∷ Sw01 ∷ Toff134 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 0 2 (Sw12 ∷ Toff034 ∷ []) (lem-comm-push-TOFF034-sw1-L c4) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 1 2 (Sw01 ∷ Toff134 ∷ []) (lem-comm-push-TOFF034-sw0-L c4) ▸ done


-- resp CCZ134 at 2: 4 steps
lem-resp-CCZ134-at-2 : WsL → ⟪ (CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CCZ234 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CCZ134-at-2 c4 = run b0
  where
  b0 : Chain (CCZ134 ∷ []) (Sw12 ∷ Sw01 ∷ CCZ234 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 0 2 (Sw12 ∷ CCZ234 ∷ []) (wl0037 c4) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 1 2 (Sw01 ∷ CCZ234 ∷ []) (sym (c₂ (Swap) (CCZ))) ▸ done


-- resp CS14 at 3: 6 steps
lem-resp-CS14-at-3 : WsL → ⟪ (CS14 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CS24 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CS14-at-3 c4 = run b0
  where
  b0 : Chain (CS14 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CS24 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 0 2 (Sw23 ∷ CS14 ∷ []) (wl0017 c4) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 1 2 (Sw12 ∷ CS24 ∷ []) (wl0013 c4) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 2 2 (Sw01 ∷ CS24 ∷ []) (sym (c₂ (Swap) (Swap ↑ • CS • Swap ↑))) ▸ done


-- resp TOFF314 at 2: 4 steps
lem-resp-TOFF314-at-2 : WsL → ⟪ (Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ Toff324 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-TOFF314-at-2 c4 = run b0
  where
  b0 : Chain (Toff314 ∷ []) (Sw12 ∷ Sw01 ∷ Toff324 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 0 2 (Sw12 ∷ Toff324 ∷ []) (sym (wl0038 c4)) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 1 2 (Sw01 ∷ Toff324 ∷ []) (sym (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI))) ▸ done


-- comm push CCZ024 sw0 L: 46 steps
lem-comm-push-CCZ024-sw0-L : WsL → ⟪ (CCZ024 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CCZ124 ∷ []) ⟫ʷ
lem-comm-push-CCZ024-sw0-L c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (run b5)))))
  where
  b0 : Chain (CCZ024 ∷ Sw01 ∷ []) (Sw12 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ [])
  b0 = at 0 1 (Sw12 ∷ CCZ014 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw34 ∷ CCZ013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸ done

  b1 : Chain (Sw12 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ []) (Sw12 ∷ CS14 ∷ CX01 ∷ Sw34 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ [])
  b1 = at 4 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0003 c4) ▸
       at 3 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸ done

  b2 : Chain (Sw12 ∷ CS14 ∷ CX01 ∷ Sw34 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ []) (CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ [])
  b2 = at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 5 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0004 c4) ▸
       at 0 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0005 c4)) ▸
       at 3 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸ done

  b3 : Chain (CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw12 ∷ Sw01 ∷ []) (CS24 ∷ CX02 ∷ CS24⁻ ∷ Sw01 ∷ CX12 ∷ CS14 ∷ [])
  b3 = at 1 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CS24⁻ ∷ Sw12 ∷ []) (sym (wl0007 c4)) ▸
       at 5 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 3 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R c4) ▸
       at 5 2 [] (wl0006 c4) ▸
       at 4 2 (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L c4) ▸
       at 3 2 (Sw01 ∷ CX12 ∷ []) (wl0039 c4) ▸ done

  b4 : Chain (CS24 ∷ CX02 ∷ CS24⁻ ∷ Sw01 ∷ CX12 ∷ CS14 ∷ []) (Sw01 ∷ Sw34 ∷ CS23 ∷ CX12 ∷ Sw34 ∷ Sw34 ∷ CS23⁻ ∷ Sw34 ∷ CX12 ∷ CS14 ∷ [])
  b4 = at 2 2 (Sw01 ∷ CS24⁻ ∷ []) (sym (c₂ (Swap) (Swap ↑ • (CS • CS • CS) • Swap ↑))) ▸
       at 1 2 (Sw01 ∷ CX12 ∷ []) (wl0039 c4) ▸
       at 0 2 (Sw01 ∷ CS24 ∷ []) (sym (c₂ (Swap) (Swap ↑ • CS • Swap ↑))) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0004 c4) ▸
       at 3 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 5 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b5 : Chain (Sw01 ∷ Sw34 ∷ CS23 ∷ CX12 ∷ Sw34 ∷ Sw34 ∷ CS23⁻ ∷ Sw34 ∷ CX12 ∷ CS14 ∷ []) (Sw01 ∷ CCZ124 ∷ [])
  b5 = at 4 2 [] (wl0004 c4) ▸
       at 5 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 7 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0004 c4) ▸
       at 2 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (CCZ124 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CCZ014 at 2: 5 steps
lem-resp-CCZ014-at-2 : WsL → ⟪ (CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CCZ124 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CCZ014-at-2 c4 = run b0
  where
  b0 : Chain (CCZ014 ∷ []) (Sw12 ∷ Sw01 ∷ CCZ124 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 1 3 (CCZ024 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 1 2 (Sw01 ∷ CCZ124 ∷ []) (lem-comm-push-CCZ024-sw0-L c4) ▸ done


-- resp CX13 at 2: 4 steps
lem-resp-CX13-at-2 : WsL → ⟪ (CX13 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CX23 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CX13-at-2 c4 = run b0
  where
  b0 : Chain (CX13 ∷ []) (Sw12 ∷ Sw01 ∷ CX23 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 0 2 (Sw12 ∷ CX23 ∷ []) (wl0019 c4) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 1 2 (Sw01 ∷ CX23 ∷ []) (sym (c₂ (Swap) (CX₀₁))) ▸ done


-- comm push TOFF204 sw0 L: 62 steps
lem-comm-push-TOFF204-sw0-L : WsL → ⟪ (Toff204 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Toff214 ∷ []) ⟫ʷ
lem-comm-push-TOFF204-sw0-L c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (Toff204 ∷ Sw01 ∷ []) (Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ [])
  b0 = at 0 1 (Sw12 ∷ Toff104 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw34 ∷ Toff103 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸ done

  b1 : Chain (Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ []) (Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ [])
  b1 = at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 10 2 [] (wl0003 c4) ▸ done

  b2 : Chain (Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ []) (Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw34 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ [])
  b2 = at 1 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 4 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 4 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸ done

  b3 : Chain (Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw34 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ []) (K2 ∷ CS24 ∷ CX02 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw01 ∷ [])
  b3 = at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 8 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 9 2 [] (wl0004 c4) ▸
       at 0 2 (K2 ∷ Sw12 ∷ []) (sym (wl0040 c4)) ▸
       at 1 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0005 c4)) ▸
       at 4 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 2 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (K2 ∷ CS24 ∷ CX02 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw01 ∷ []) (K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K2 ∷ Sw01 ∷ ι ∷ [])
  b4 = at 3 2 (CS24⁻ ∷ Sw12 ∷ []) (sym (wl0007 c4)) ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R c4) ▸
       at 6 2 (K2 ∷ Sw12 ∷ []) (sym (wl0040 c4)) ▸
       at 7 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 8 2 [] (wl0006 c4) ▸
       at 7 2 (Sw01 ∷ ι ∷ []) (sym (wl0025 c4)) ▸ done

  b5 : Chain (K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K2 ∷ Sw01 ∷ ι ∷ []) (Sw01 ∷ Sw34 ∷ Sw34 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2 ∷ ι ∷ [])
  b5 = at 6 2 (Sw01 ∷ K2 ∷ []) (sym (c₂ (Swap) (K))) ▸
       at 5 2 (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L c4) ▸
       at 4 2 (Sw01 ∷ CX12 ∷ []) (wl0039 c4) ▸
       at 3 2 (Sw01 ∷ CS24⁻ ∷ []) (sym (c₂ (Swap) (Swap ↑ • (CS • CS • CS) • Swap ↑))) ▸
       at 2 2 (Sw01 ∷ CX12 ∷ []) (wl0039 c4) ▸
       at 1 2 (Sw01 ∷ CS24 ∷ []) (sym (c₂ (Swap) (Swap ↑ • CS • Swap ↑))) ▸
       at 0 2 (Sw01 ∷ K2 ∷ []) (sym (c₂ (Swap) (K))) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸ done

  b6 : Chain (Sw01 ∷ Sw34 ∷ Sw34 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2 ∷ ι ∷ []) (Sw01 ∷ Sw34 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw34 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ K2 ∷ ι ∷ [])
  b6 = at 2 2 (K2 ∷ Sw34 ∷ []) (sym (c₃ (K ↑ ↑) (Swap))) ▸
       at 4 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0004 c4) ▸
       at 4 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 6 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0004 c4) ▸
       at 6 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 8 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b7 : Chain (Sw01 ∷ Sw34 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw34 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ K2 ∷ ι ∷ []) (Sw01 ∷ Toff214 ∷ [])
  b7 = at 7 2 [] (wl0004 c4) ▸
       at 8 2 (K2 ∷ Sw34 ∷ []) (sym (c₃ (K ↑ ↑) (Swap))) ▸
       at 9 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 2 8 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (wl0041 c4) ▸
       at 2 8 (Toff213 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff214 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp TOFF204 at 1: 2 steps
lem-resp-TOFF204-at-1 : WsL → ⟪ (Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Toff214 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-TOFF204-at-1 c4 = run b0
  where
  b0 : Chain (Toff204 ∷ []) (Sw01 ∷ Toff214 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 0 2 (Sw01 ∷ Toff214 ∷ []) (lem-comm-push-TOFF204-sw0-L c4) ▸ done


-- resp CCZ024 at 1: 2 steps
lem-resp-CCZ024-at-1 : WsL → ⟪ (CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CCZ124 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CCZ024-at-1 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ []) (Sw01 ∷ CCZ124 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 0 2 (Sw01 ∷ CCZ124 ∷ []) (lem-comm-push-CCZ024-sw0-L c4) ▸ done


-- comm push CSd04 sw0 L: 5 steps
lem-comm-push-CSd04-sw0-L : WsL → ⟪ (CS04⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CS14⁻ ∷ []) ⟫ʷ
lem-comm-push-CSd04-sw0-L c4 = run b0
  where
  b0 : Chain (CS04⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS14⁻ ∷ [])
  b0 = at 0 1 (Sw34 ∷ CS03⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 1 2 (Sw01 ∷ CS13⁻ ∷ []) (wl0042 c4) ▸
       at 0 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 1 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CSd04 at 1: 2 steps
lem-resp-CSd04-at-1 : WsL → ⟪ (CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CS14⁻ ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CSd04-at-1 c4 = run b0
  where
  b0 : Chain (CS04⁻ ∷ []) (Sw01 ∷ CS14⁻ ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 0 2 (Sw01 ∷ CS14⁻ ∷ []) (lem-comm-push-CSd04-sw0-L c4) ▸ done


-- comm TOFF204 CSd13: 11 steps
lem-comm-TOFF204-CSd13 : WsL → ⟪ (Toff204 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ Toff204 ∷ []) ⟫ʷ
lem-comm-TOFF204-CSd13 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff204 ∷ CS13⁻ ∷ []) (Sw12 ∷ Sw34 ∷ Sw34 ∷ CS23⁻ ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ [])
  b0 = at 0 1 (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS23⁻ ∷ Sw12 ∷ []) (sym (wl0029 c4)) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 5 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0009 c4)) ▸
       at 3 2 (CS34⁻ ∷ Toff102 ∷ []) (c₃ (K ↑ • CCZ • K ↑ • iI) (CS • CS • CS)) ▸
       at 2 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0012 c4)) ▸
       at 2 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ Sw34 ∷ Sw34 ∷ CS23⁻ ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) (CS13⁻ ∷ Toff204 ∷ [])
  b1 = at 1 2 [] (wl0004 c4) ▸
       at 0 2 (CS13⁻ ∷ Sw12 ∷ []) (sym (wl0028 c4)) ▸
       at 1 7 (Toff204 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm push CSd04 sw1 L: 5 steps
lem-comm-push-CSd04-sw1-L : WsL → ⟪ (CS04⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CS04⁻ ∷ []) ⟫ʷ
lem-comm-push-CSd04-sw1-L c4 = run b0
  where
  b0 : Chain (CS04⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS04⁻ ∷ [])
  b0 = at 0 1 (Sw34 ∷ CS03⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 1 2 (Sw12 ∷ CS03⁻ ∷ []) (wl0043 c4) ▸
       at 0 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 1 3 (CS04⁻ ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CSd04 at 2: 4 steps
lem-resp-CSd04-at-2 : WsL → ⟪ (CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CS14⁻ ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CSd04-at-2 c4 = run b0
  where
  b0 : Chain (CS04⁻ ∷ []) (Sw12 ∷ Sw01 ∷ CS14⁻ ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 0 2 (Sw12 ∷ CS04⁻ ∷ []) (lem-comm-push-CSd04-sw1-L c4) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 1 2 (Sw01 ∷ CS14⁻ ∷ []) (lem-comm-push-CSd04-sw0-L c4) ▸ done


-- resp CSd13 at 2: 4 steps
lem-resp-CSd13-at-2 : WsL → ⟪ (CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CSd13-at-2 c4 = run b0
  where
  b0 : Chain (CS13⁻ ∷ []) (Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 0 2 (Sw12 ∷ CS23⁻ ∷ []) (wl0028 c4) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 1 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (c₂ (Swap) (CS • CS • CS))) ▸ done


-- comm push CX04 sw0 L: 5 steps
lem-comm-push-CX04-sw0-L : WsL → ⟪ (CX04 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CX14 ∷ []) ⟫ʷ
lem-comm-push-CX04-sw0-L c4 = run b0
  where
  b0 : Chain (CX04 ∷ Sw01 ∷ []) (Sw01 ∷ CX14 ∷ [])
  b0 = at 0 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 1 2 (Sw01 ∷ CX13 ∷ []) (wl0016 c4) ▸
       at 0 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 1 3 (CX14 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CX04 at 1: 2 steps
lem-resp-CX04-at-1 : WsL → ⟪ (CX04 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CX14 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CX04-at-1 c4 = run b0
  where
  b0 : Chain (CX04 ∷ []) (Sw01 ∷ CX14 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 0 2 (Sw01 ∷ CX14 ∷ []) (lem-comm-push-CX04-sw0-L c4) ▸ done


-- comm CX04 CCZ123: 13 steps
lem-comm-CX04-CCZ123 : WsL → ⟪ (CX04 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CX04 ∷ []) ⟫ʷ
lem-comm-CX04-CCZ123 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX04 ∷ CCZ123 ∷ []) (Sw34 ∷ Sw23 ∷ CCZ134 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 6 3 (CCZ124 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 5 3 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0044 c4)) ▸
       at 3 2 (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ)) ▸
       at 2 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ CCZ134 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (CCZ123 ∷ CX04 ∷ [])
  b1 = at 2 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0003 c4) ▸
       at 1 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0004 c4) ▸
       at 1 7 (CX04 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CSd04 TOFF213: 13 steps
lem-comm-CSd04-TOFF213 : WsL → ⟪ (CS04⁻ ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CS04⁻ ∷ []) ⟫ʷ
lem-comm-CSd04-TOFF213 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS04⁻ ∷ Toff213 ∷ []) (Sw34 ∷ Sw23 ∷ Toff314 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 6 3 (Toff214 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 5 3 (Toff314 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Toff324 ∷ Sw12 ∷ []) (wl0045 c4) ▸
       at 3 2 (Toff324 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 2 2 (Toff314 ∷ Sw12 ∷ []) (wl0038 c4) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Toff314 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (Toff213 ∷ CS04⁻ ∷ [])
  b1 = at 2 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0003 c4) ▸
       at 1 1 (Sw34 ∷ Toff213 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0004 c4) ▸
       at 1 7 (CS04⁻ ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CCZ024 at 3: 7 steps
lem-resp-CCZ024-at-3 : WsL → ⟪ (CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CCZ134 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CCZ024-at-3 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CCZ134 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (CCZ034 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 1 2 (Sw12 ∷ CCZ034 ∷ []) (lem-comm-push-CCZ034-sw1-L c4) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 2 2 (Sw01 ∷ CCZ134 ∷ []) (lem-comm-push-CCZ034-sw0-L c4) ▸ done


-- resp CS03 at 1: 2 steps
lem-resp-CS03-at-1 : WsL → ⟪ (CS03 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CS13 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CS03-at-1 c4 = run b0
  where
  b0 : Chain (CS03 ∷ []) (Sw01 ∷ CS13 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 0 2 (Sw01 ∷ CS13 ∷ []) (wl0015 c4) ▸ done


-- comm CSd13 CCZ024: 11 steps
lem-comm-CSd13-CCZ024 : WsL → ⟪ (CS13⁻ ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-comm-CSd13-CCZ024 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS13⁻ ∷ CCZ024 ∷ []) (Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ CS23⁻ ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ CS23⁻ ∷ []) (wl0028 c4) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw23 ∷ CS34⁻ ∷ []) (wl0012 c4) ▸
       at 3 2 (CCZ012 ∷ CS34⁻ ∷ []) (sym (c₃ (CCZ) (CS • CS • CS))) ▸
       at 4 2 (Sw23 ∷ CS24⁻ ∷ []) (wl0009 c4) ▸
       at 5 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ CS23⁻ ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ []) (CCZ024 ∷ CS13⁻ ∷ [])
  b1 = at 7 2 [] (wl0004 c4) ▸
       at 6 2 (Sw12 ∷ CS13⁻ ∷ []) (wl0029 c4) ▸
       at 0 7 (CCZ024 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CS13 CCZ024: 11 steps
lem-comm-CS13-CCZ024 : WsL → ⟪ (CS13 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ CS13 ∷ []) ⟫ʷ
lem-comm-CS13-CCZ024 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS13 ∷ CCZ024 ∷ []) (Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ CS23 ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ CS23 ∷ []) (wl0046 c4) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 3 (CS24 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw23 ∷ CS34 ∷ []) (wl0011 c4) ▸
       at 3 2 (CCZ012 ∷ CS34 ∷ []) (sym (c₃ (CCZ) (CS))) ▸
       at 4 2 (Sw23 ∷ CS24 ∷ []) (wl0008 c4) ▸
       at 5 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ CS23 ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ []) (CCZ024 ∷ CS13 ∷ [])
  b1 = at 7 2 [] (wl0004 c4) ▸
       at 6 2 (Sw12 ∷ CS13 ∷ []) (wl0047 c4) ▸
       at 0 7 (CCZ024 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CSd03 at 1: 2 steps
lem-resp-CSd03-at-1 : WsL → ⟪ (CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CS13⁻ ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CSd03-at-1 c4 = run b0
  where
  b0 : Chain (CS03⁻ ∷ []) (Sw01 ∷ CS13⁻ ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 0 2 (Sw01 ∷ CS13⁻ ∷ []) (wl0042 c4) ▸ done


-- comm CX13 CCZ024: 11 steps
lem-comm-CX13-CCZ024 : WsL → ⟪ (CX13 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ CX13 ∷ []) ⟫ʷ
lem-comm-CX13-CCZ024 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX13 ∷ CCZ024 ∷ []) (Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ CX23 ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ CX23 ∷ []) (wl0019 c4) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 3 (CX24 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw23 ∷ CX34 ∷ []) (wl0020 c4) ▸
       at 3 2 (CCZ012 ∷ CX34 ∷ []) (sym (c₃ (CCZ) (CX₀₁))) ▸
       at 4 2 (Sw23 ∷ CX24 ∷ []) (wl0021 c4) ▸
       at 5 1 (Sw34 ∷ CX23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ CX23 ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ []) (CCZ024 ∷ CX13 ∷ [])
  b1 = at 7 2 [] (wl0004 c4) ▸
       at 6 2 (Sw12 ∷ CX13 ∷ []) (wl0022 c4) ▸
       at 0 7 (CCZ024 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm push CS04 sw2 L: 7 steps
lem-comm-push-CS04-sw2-L : WsL → ⟪ (CS04 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ CS04 ∷ []) ⟫ʷ
lem-comm-push-CS04-sw2-L c4 = run b0
  where
  b0 : Chain (CS04 ∷ Sw23 ∷ []) (Sw23 ∷ CS04 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0002 c4) ▸
       at 4 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 3 2 (Sw34 ∷ CS01 ∷ []) (c₂ (CS) (Swap ↑)) ▸
       at 2 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 0 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (sym (wl0002 c4)) ▸
       at 1 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm push CCZ014 sw2 L: 47 steps
lem-comm-push-CCZ014-sw2-L : WsL → ⟪ (CCZ014 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ CCZ014 ∷ []) ⟫ʷ
lem-comm-push-CCZ014-sw2-L c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (run b5)))))
  where
  b0 : Chain (CCZ014 ∷ Sw23 ∷ []) (Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw34 ∷ Sw23 ∷ [])
  b0 = at 0 1 (Sw34 ∷ CCZ013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 3 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (CS14 ∷ CX01 ∷ Sw34 ∷ CS13⁻ ∷ Sw34 ∷ Sw34 ∷ CX01 ∷ CS03 ∷ Sw34 ∷ Sw23 ∷ [])
  b1 = at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0003 c4) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 0 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 4 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸ done

  b2 : Chain (CS14 ∷ CX01 ∷ Sw34 ∷ CS13⁻ ∷ Sw34 ∷ Sw34 ∷ CX01 ∷ CS03 ∷ Sw34 ∷ Sw23 ∷ []) (CS14 ∷ CX01 ∷ Sw23 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ [])
  b2 = at 2 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 4 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0004 c4) ▸
       at 4 2 (Sw23 ∷ CS04 ∷ []) (lem-comm-push-CS04-sw2-L c4) ▸
       at 3 2 (Sw23 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Swap)) ▸
       at 2 2 (Sw23 ∷ CS14⁻ ∷ []) (wl0048 c4) ▸ done

  b3 : Chain (CS14 ∷ CX01 ∷ Sw23 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) (Sw23 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw34 ∷ CX01 ∷ CS04 ∷ [])
  b3 = at 1 2 (Sw23 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Swap)) ▸
       at 0 2 (Sw23 ∷ CS14 ∷ []) (wl0017 c4) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0004 c4) ▸
       at 3 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 5 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0004 c4) ▸ done

  b4 : Chain (Sw23 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw34 ∷ CX01 ∷ CS04 ∷ []) (Sw23 ∷ Sw34 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ Sw23 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ Sw34 ∷ [])
  b4 = at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0004 c4) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0003 c4) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b5 : Chain (Sw23 ∷ Sw34 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ Sw23 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ Sw34 ∷ []) (Sw23 ∷ CCZ014 ∷ [])
  b5 = at 5 2 [] (wl0003 c4) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0003 c4) ▸
       at 3 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (CCZ014 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CCZ014 at 3: 7 steps
lem-resp-CCZ014-at-3 : WsL → ⟪ (CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CCZ124 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CCZ014-at-3 c4 = run b0
  where
  b0 : Chain (CCZ014 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CCZ124 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 0 2 (Sw23 ∷ CCZ014 ∷ []) (lem-comm-push-CCZ014-sw2-L c4) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 2 3 (CCZ024 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 2 2 (Sw01 ∷ CCZ124 ∷ []) (lem-comm-push-CCZ024-sw0-L c4) ▸ done


-- resp CS03 at 2: 4 steps
lem-resp-CS03-at-2 : WsL → ⟪ (CS03 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CS13 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CS03-at-2 c4 = run b0
  where
  b0 : Chain (CS03 ∷ []) (Sw12 ∷ Sw01 ∷ CS13 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 0 2 (Sw12 ∷ CS03 ∷ []) (wl0001 c4) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 1 2 (Sw01 ∷ CS13 ∷ []) (wl0015 c4) ▸ done


-- resp CS14 at 2: 4 steps
lem-resp-CS14-at-2 : WsL → ⟪ (CS14 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CS24 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CS14-at-2 c4 = run b0
  where
  b0 : Chain (CS14 ∷ []) (Sw12 ∷ Sw01 ∷ CS24 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 0 2 (Sw12 ∷ CS24 ∷ []) (wl0013 c4) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 1 2 (Sw01 ∷ CS24 ∷ []) (sym (c₂ (Swap) (Swap ↑ • CS • Swap ↑))) ▸ done


-- comm push CX04 sw1 L: 5 steps
lem-comm-push-CX04-sw1-L : WsL → ⟪ (CX04 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CX04 ∷ []) ⟫ʷ
lem-comm-push-CX04-sw1-L c4 = run b0
  where
  b0 : Chain (CX04 ∷ Sw12 ∷ []) (Sw12 ∷ CX04 ∷ [])
  b0 = at 0 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 1 2 (Sw12 ∷ CX03 ∷ []) (wl0010 c4) ▸
       at 0 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 1 3 (CX04 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CX04 at 2: 4 steps
lem-resp-CX04-at-2 : WsL → ⟪ (CX04 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CX14 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CX04-at-2 c4 = run b0
  where
  b0 : Chain (CX04 ∷ []) (Sw12 ∷ Sw01 ∷ CX14 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 0 2 (Sw12 ∷ CX04 ∷ []) (lem-comm-push-CX04-sw1-L c4) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 1 2 (Sw01 ∷ CX14 ∷ []) (lem-comm-push-CX04-sw0-L c4) ▸ done


-- resp CSd14 at 2: 4 steps
lem-resp-CSd14-at-2 : WsL → ⟪ (CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CS24⁻ ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CSd14-at-2 c4 = run b0
  where
  b0 : Chain (CS14⁻ ∷ []) (Sw12 ∷ Sw01 ∷ CS24⁻ ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 0 2 (Sw12 ∷ CS24⁻ ∷ []) (wl0014 c4) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 1 2 (Sw01 ∷ CS24⁻ ∷ []) (sym (c₂ (Swap) (Swap ↑ • (CS • CS • CS) • Swap ↑))) ▸ done


-- comm CX04 TOFF213: 13 steps
lem-comm-CX04-TOFF213 : WsL → ⟪ (CX04 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CX04 ∷ []) ⟫ʷ
lem-comm-CX04-TOFF213 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX04 ∷ Toff213 ∷ []) (Sw34 ∷ Sw23 ∷ Toff314 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 6 3 (Toff214 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 5 3 (Toff314 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Toff324 ∷ Sw12 ∷ []) (wl0045 c4) ▸
       at 3 2 (Toff324 ∷ CX01 ∷ []) (c₂ (CX₀₁) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 2 2 (Toff314 ∷ Sw12 ∷ []) (wl0038 c4) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Toff314 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (Toff213 ∷ CX04 ∷ [])
  b1 = at 2 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0003 c4) ▸
       at 1 1 (Sw34 ∷ Toff213 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0004 c4) ▸
       at 1 7 (CX04 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp TOFF214 at 3: 7 steps
lem-resp-TOFF214-at-3 : WsL → ⟪ (Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff324 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-TOFF214-at-3 c4 = run b0
  where
  b0 : Chain (Toff214 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff324 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (Toff314 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 1 2 (Sw12 ∷ Toff324 ∷ []) (sym (wl0038 c4)) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 2 2 (Sw01 ∷ Toff324 ∷ []) (sym (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI))) ▸ done


-- comm push CZ04 sw0 L: 5 steps
lem-comm-push-CZ04-sw0-L : WsL → ⟪ (CZ04 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CZ14 ∷ []) ⟫ʷ
lem-comm-push-CZ04-sw0-L c4 = run b0
  where
  b0 : Chain (CZ04 ∷ Sw01 ∷ []) (Sw01 ∷ CZ14 ∷ [])
  b0 = at 0 1 (Sw34 ∷ CZ03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 1 2 (Sw01 ∷ CZ13 ∷ []) (wl0049 c4) ▸
       at 0 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 1 3 (CZ14 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CZ04 at 1: 2 steps
lem-resp-CZ04-at-1 : WsL → ⟪ (CZ04 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CZ14 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CZ04-at-1 c4 = run b0
  where
  b0 : Chain (CZ04 ∷ []) (Sw01 ∷ CZ14 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 0 2 (Sw01 ∷ CZ14 ∷ []) (lem-comm-push-CZ04-sw0-L c4) ▸ done


-- comm CZ04 CCZ123: 13 steps
lem-comm-CZ04-CCZ123 : WsL → ⟪ (CZ04 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CZ04 ∷ []) ⟫ʷ
lem-comm-CZ04-CCZ123 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CZ04 ∷ CCZ123 ∷ []) (Sw34 ∷ Sw23 ∷ CCZ134 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 6 3 (CCZ124 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 5 3 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0044 c4)) ▸
       at 3 2 (CCZ234 ∷ CZ01 ∷ []) (c₂ (CZ) (CCZ)) ▸
       at 2 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ CCZ134 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (CCZ123 ∷ CZ04 ∷ [])
  b1 = at 2 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0003 c4) ▸
       at 1 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0004 c4) ▸
       at 1 7 (CZ04 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CZ04 TOFF213: 13 steps
lem-comm-CZ04-TOFF213 : WsL → ⟪ (CZ04 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CZ04 ∷ []) ⟫ʷ
lem-comm-CZ04-TOFF213 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CZ04 ∷ Toff213 ∷ []) (Sw34 ∷ Sw23 ∷ Toff314 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 6 3 (Toff214 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 5 3 (Toff314 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Toff324 ∷ Sw12 ∷ []) (wl0045 c4) ▸
       at 3 2 (Toff324 ∷ CZ01 ∷ []) (c₂ (CZ) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 2 2 (Toff314 ∷ Sw12 ∷ []) (wl0038 c4) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Toff314 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (Toff213 ∷ CZ04 ∷ [])
  b1 = at 2 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0003 c4) ▸
       at 1 1 (Sw34 ∷ Toff213 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0004 c4) ▸
       at 1 7 (CZ04 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CSd03 at 2: 4 steps
lem-resp-CSd03-at-2 : WsL → ⟪ (CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CS13⁻ ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CSd03-at-2 c4 = run b0
  where
  b0 : Chain (CS03⁻ ∷ []) (Sw12 ∷ Sw01 ∷ CS13⁻ ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 0 2 (Sw12 ∷ CS03⁻ ∷ []) (wl0043 c4) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 1 2 (Sw01 ∷ CS13⁻ ∷ []) (wl0042 c4) ▸ done


-- comm push TOFF024 sw0 L: 62 steps
lem-comm-push-TOFF024-sw0-L : WsL → ⟪ (Toff024 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Toff124 ∷ []) ⟫ʷ
lem-comm-push-TOFF024-sw0-L c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (Toff024 ∷ Sw01 ∷ []) (Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ [])
  b0 = at 0 1 (Sw12 ∷ Toff014 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸ done

  b1 : Chain (Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ []) (Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ [])
  b1 = at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 10 2 [] (wl0003 c4) ▸ done

  b2 : Chain (Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ []) (Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ [])
  b2 = at 1 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 4 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 4 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸ done

  b3 : Chain (Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ []) (K0 ∷ CS24 ∷ CX02 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw01 ∷ [])
  b3 = at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 8 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 9 2 [] (wl0004 c4) ▸
       at 0 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 1 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0005 c4)) ▸
       at 4 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 2 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (K0 ∷ CS24 ∷ CX02 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw01 ∷ []) (K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0 ∷ Sw01 ∷ ι ∷ [])
  b4 = at 3 2 (CS24⁻ ∷ Sw12 ∷ []) (sym (wl0007 c4)) ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R c4) ▸
       at 6 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 7 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 8 2 [] (wl0006 c4) ▸
       at 7 2 (Sw01 ∷ ι ∷ []) (sym (wl0025 c4)) ▸ done

  b5 : Chain (K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0 ∷ Sw01 ∷ ι ∷ []) (Sw01 ∷ Sw34 ∷ Sw34 ∷ K1 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K1 ∷ ι ∷ [])
  b5 = at 6 2 (Sw01 ∷ K1 ∷ []) (wl0026 c4) ▸
       at 5 2 (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L c4) ▸
       at 4 2 (Sw01 ∷ CX12 ∷ []) (wl0039 c4) ▸
       at 3 2 (Sw01 ∷ CS24⁻ ∷ []) (sym (c₂ (Swap) (Swap ↑ • (CS • CS • CS) • Swap ↑))) ▸
       at 2 2 (Sw01 ∷ CX12 ∷ []) (wl0039 c4) ▸
       at 1 2 (Sw01 ∷ CS24 ∷ []) (sym (c₂ (Swap) (Swap ↑ • CS • Swap ↑))) ▸
       at 0 2 (Sw01 ∷ K1 ∷ []) (wl0026 c4) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸ done

  b6 : Chain (Sw01 ∷ Sw34 ∷ Sw34 ∷ K1 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K1 ∷ ι ∷ []) (Sw01 ∷ Sw34 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw34 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ K1 ∷ ι ∷ [])
  b6 = at 2 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 4 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0004 c4) ▸
       at 4 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 6 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0004 c4) ▸
       at 6 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 8 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b7 : Chain (Sw01 ∷ Sw34 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw34 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ K1 ∷ ι ∷ []) (Sw01 ∷ Toff124 ∷ [])
  b7 = at 7 2 [] (wl0004 c4) ▸
       at 8 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 9 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 2 8 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (wl0027 c4) ▸
       at 2 8 (Toff123 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff124 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp TOFF014 at 2: 5 steps
lem-resp-TOFF014-at-2 : WsL → ⟪ (Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ Toff124 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-TOFF014-at-2 c4 = run b0
  where
  b0 : Chain (Toff014 ∷ []) (Sw12 ∷ Sw01 ∷ Toff124 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 1 3 (Toff024 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 1 2 (Sw01 ∷ Toff124 ∷ []) (lem-comm-push-TOFF024-sw0-L c4) ▸ done


-- comm TOFF014 CSd23: 9 steps
lem-comm-TOFF014-CSd23 : WsL → ⟪ (Toff014 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ Toff014 ∷ []) ⟫ʷ
lem-comm-TOFF014-CSd23 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff014 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 4 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0009 c4)) ▸
       at 2 2 (CS34⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (CS • CS • CS)) ▸
       at 1 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0012 c4)) ▸
       at 1 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0004 c4) ▸ done

  b1 : Chain (CS23⁻ ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ []) (CS23⁻ ∷ Toff014 ∷ [])
  b1 = at 1 5 (Toff014 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CS04 at 2: 4 steps
lem-resp-CS04-at-2 : WsL → ⟪ (CS04 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CS14 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CS04-at-2 c4 = run b0
  where
  b0 : Chain (CS04 ∷ []) (Sw12 ∷ Sw01 ∷ CS14 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 0 2 (Sw12 ∷ CS04 ∷ []) (lem-comm-push-CS04-sw1-L c4) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 1 2 (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L c4) ▸ done


-- resp CX14 at 2: 4 steps
lem-resp-CX14-at-2 : WsL → ⟪ (CX14 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CX24 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CX14-at-2 c4 = run b0
  where
  b0 : Chain (CX14 ∷ []) (Sw12 ∷ Sw01 ∷ CX24 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 0 2 (Sw12 ∷ CX24 ∷ []) (wl0050 c4) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 1 2 (Sw01 ∷ CX24 ∷ []) (sym (c₂ (Swap) (Swap ↑ • CX₀₁ • Swap ↑))) ▸ done


-- comm CX14 CCZ023: 7 steps
lem-comm-CX14-CCZ023 : WsL → ⟪ (CX14 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ CX14 ∷ []) ⟫ʷ
lem-comm-CX14-CCZ023 c4 = run b0
  where
  b0 : Chain (CX14 ∷ CCZ023 ∷ []) (CCZ023 ∷ CX14 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ CX24 ∷ []) (wl0050 c4) ▸
       at 1 2 (Sw23 ∷ CX34 ∷ []) (wl0020 c4) ▸
       at 2 2 (CCZ012 ∷ CX34 ∷ []) (sym (c₃ (CCZ) (CX₀₁))) ▸
       at 3 2 (Sw23 ∷ CX24 ∷ []) (wl0021 c4) ▸
       at 4 2 (Sw12 ∷ CX14 ∷ []) (wl0051 c4) ▸
       at 0 5 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CCZ023 at 1: 2 steps
lem-resp-CCZ023-at-1 : WsL → ⟪ (CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CCZ023-at-1 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ []) (Sw01 ∷ CCZ123 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 0 2 (Sw01 ∷ CCZ123 ∷ []) (wl0030 c4) ▸ done


-- resp CS04 at 1: 2 steps
lem-resp-CS04-at-1 : WsL → ⟪ (CS04 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CS14 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CS04-at-1 c4 = run b0
  where
  b0 : Chain (CS04 ∷ []) (Sw01 ∷ CS14 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 0 2 (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L c4) ▸ done


-- comm CSd14 TOFF023: 7 steps
lem-comm-CSd14-TOFF023 : WsL → ⟪ (CS14⁻ ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CS14⁻ ∷ []) ⟫ʷ
lem-comm-CSd14-TOFF023 c4 = run b0
  where
  b0 : Chain (CS14⁻ ∷ Toff023 ∷ []) (Toff023 ∷ CS14⁻ ∷ [])
  b0 = at 1 1 (Sw12 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ CS24⁻ ∷ []) (wl0014 c4) ▸
       at 1 2 (Sw23 ∷ CS34⁻ ∷ []) (wl0012 c4) ▸
       at 2 2 (Toff012 ∷ CS34⁻ ∷ []) (sym (c₃ (Toff) (CS • CS • CS))) ▸
       at 3 2 (Sw23 ∷ CS24⁻ ∷ []) (wl0009 c4) ▸
       at 4 2 (Sw12 ∷ CS14⁻ ∷ []) (wl0007 c4) ▸
       at 0 5 (Toff023 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CS13 at 2: 4 steps
lem-resp-CS13-at-2 : WsL → ⟪ (CS13 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CS23 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CS13-at-2 c4 = run b0
  where
  b0 : Chain (CS13 ∷ []) (Sw12 ∷ Sw01 ∷ CS23 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 0 2 (Sw12 ∷ CS23 ∷ []) (wl0046 c4) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 1 2 (Sw01 ∷ CS23 ∷ []) (sym (c₂ (Swap) (CS))) ▸ done


-- comm CSd23 CCZ014: 9 steps
lem-comm-CSd23-CCZ014 : WsL → ⟪ (CS23⁻ ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ CS23⁻ ∷ []) ⟫ʷ
lem-comm-CSd23-CCZ014 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS23⁻ ∷ CCZ014 ∷ []) (Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ CS23⁻ ∷ [])
  b0 = at 1 1 (Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw23 ∷ CS34⁻ ∷ []) (wl0012 c4) ▸
       at 2 2 (CCZ012 ∷ CS34⁻ ∷ []) (sym (c₃ (CCZ) (CS • CS • CS))) ▸
       at 3 2 (Sw23 ∷ CS24⁻ ∷ []) (wl0009 c4) ▸
       at 4 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0004 c4) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ CS23⁻ ∷ []) (CCZ014 ∷ CS23⁻ ∷ [])
  b1 = at 0 5 (CCZ014 ∷ []) (by-assoc Eq.refl) ▸ done


{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.FiveV.D.R007 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.FiveV.WinSig using (WsL ; wl0001 ; wl0002 ; wl0003 ; wl0004 ; wl0005 ; wl0006 ; wl0007 ; wl0008 ; wl0009 ; wl0010 ; wl0011 ; wl0012 ; wl0013 ; wl0014 ; wl0029 ; wl0035 ; wl0047 ; wl0053 ; wl0063 ; wl0064 ; wl0065 ; wl0066 ; wl0067 ; wl0109 ; wl0117 ; wl0118 ; wl0119 ; wl0125 ; wl0126 ; wl0127 ; wl0128 ; wl0129 ; wl0130 ; wl0131 ; wl0132 ; wl0133)
open import Examples.Groups.Clifford+CS.FiveV.Chain
open import Examples.Groups.Clifford+CS.FiveV.D.R001 using (lem-comm-push-CCZ014-sw2-L ; lem-comm-push-CCZ034-sw1-L ; lem-comm-push-CS04-sw1-R ; lem-comm-push-CS04-sw2-R ; lem-comm-push-TOFF034-sw1-L)
open import Examples.Groups.Clifford+CS.FiveV.D.R002 using (lem-comm-push-TOFF401-sw2-L)
open import Examples.Groups.Clifford+CS.FiveV.D.R004 using (lem-comm-push-CCZ024-sw3-L)
open import Examples.Groups.Clifford+CS.FiveV.D.R005 using (lem-comm-push-TOFF402-sw3-L)
open import Examples.Groups.Clifford+CS.FiveV.D.R006 using (lem-comm-push-BOX⟨4·103⟩-sw0-L ; lem-comm-push-CCZ124-sw0-L ; lem-comm-push-CS14-sw0-L)
-- comm push TOFF124 sw0 L: 62 steps
lem-comm-push-TOFF124-sw0-L : WsL → ⟪ (Toff124 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Toff024 ∷ []) ⟫ʷ
lem-comm-push-TOFF124-sw0-L c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (Toff124 ∷ Sw01 ∷ []) (K1 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Sw34 ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw34 ∷ Sw01 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Toff123 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 3 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 3 (CS24 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (K1 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Sw34 ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw34 ∷ Sw01 ∷ []) (K1 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Sw01 ∷ K0 ∷ ι1 ∷ [])
  b1 = at 4 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 5 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 7 2 (ι1 ∷ Sw34 ∷ []) (sym (c₂ (iI ↑) (Swap ↑))) ▸
       at 8 2 [] (wl0004 c4) ▸
       at 7 2 (Sw01 ∷ ι1 ∷ []) (sym (wl0118 c4)) ▸
       at 6 2 (Sw01 ∷ K0 ∷ []) (wl0109 c4) ▸ done

  b2 : Chain (K1 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Sw01 ∷ K0 ∷ ι1 ∷ []) (Sw01 ∷ Sw12 ∷ K0 ∷ Sw12 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0 ∷ ι1 ∷ [])
  b2 = at 5 2 (Sw01 ∷ CS04 ∷ []) (lem-comm-push-CS14-sw0-L c4) ▸
       at 4 2 (Sw01 ∷ CX02 ∷ []) (wl0117 c4) ▸
       at 3 2 (Sw01 ∷ CS24⁻ ∷ []) (sym (c₂ (Swap) (Swap ↑ • (CS • CS • CS) • Swap ↑))) ▸
       at 2 2 (Sw01 ∷ CX02 ∷ []) (wl0117 c4) ▸
       at 1 2 (Sw01 ∷ CS24 ∷ []) (sym (c₂ (Swap) (Swap ↑ • CS • Swap ↑))) ▸
       at 0 2 (Sw01 ∷ K0 ∷ []) (wl0109 c4) ▸
       at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 2 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸ done

  b3 : Chain (Sw01 ∷ Sw12 ∷ K0 ∷ Sw12 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0 ∷ ι1 ∷ []) (Sw01 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ Sw12 ∷ ι1 ∷ [])
  b3 = at 3 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 c4)) ▸
       at 5 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0006 c4) ▸
       at 5 2 (CS14⁻ ∷ Sw12 ∷ []) (sym (wl0014 c4)) ▸
       at 7 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0006 c4) ▸
       at 7 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R c4) ▸
       at 8 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸ done

  b4 : Chain (Sw01 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ Sw12 ∷ ι1 ∷ []) (Sw01 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw34 ∷ CX01 ∷ CS04 ∷ K0 ∷ ι1 ∷ Sw12 ∷ [])
  b4 = at 9 2 (ι1 ∷ Sw12 ∷ []) (wl0119 c4) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 5 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0004 c4) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0004 c4) ▸ done

  b5 : Chain (Sw01 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw34 ∷ CX01 ∷ CS04 ∷ K0 ∷ ι1 ∷ Sw12 ∷ []) (Sw01 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι1 ∷ Sw34 ∷ Sw12 ∷ [])
  b5 = at 7 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 9 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0004 c4) ▸
       at 9 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 10 2 (ι1 ∷ Sw34 ∷ []) (sym (c₂ (iI ↑) (Swap ↑))) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b6 : Chain (Sw01 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι1 ∷ Sw34 ∷ Sw12 ∷ []) (Sw01 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ Sw23 ∷ ι1 ∷ Sw34 ∷ Sw12 ∷ [])
  b6 = at 5 2 [] (wl0003 c4) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0003 c4) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (wl0003 c4) ▸
       at 10 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸ done

  b7 : Chain (Sw01 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ Sw23 ∷ ι1 ∷ Sw34 ∷ Sw12 ∷ []) (Sw01 ∷ Toff024 ∷ [])
  b7 = at 11 2 (ι1 ∷ Sw23 ∷ []) (sym (c₂ (iI ↑) (Swap))) ▸
       at 4 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (sym (wl0125 c4)) ▸
       at 4 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff014 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff024 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm push BOX(1;4203) sw0 L: 8 steps
lem-comm-push-BOX⟨1·4203⟩-sw0-L : WsL → ⟪ (Bx1-4203 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Bx0-4213 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨1·4203⟩-sw0-L c4 = run b0
  where
  b0 : Chain (Bx1-4203 ∷ Sw01 ∷ []) (Sw01 ∷ Bx0-4213 ∷ [])
  b0 = at 0 1 (CCZ124 ∷ Toff124 ∷ Bx4-103 ∷ Toff124 ∷ CCZ124 ∷ Bx4-103 ∷ []) (refl) ▸
       at 5 2 (Sw01 ∷ Bx4-013 ∷ []) (lem-comm-push-BOX⟨4·103⟩-sw0-L c4) ▸
       at 4 2 (Sw01 ∷ CCZ024 ∷ []) (lem-comm-push-CCZ124-sw0-L c4) ▸
       at 3 2 (Sw01 ∷ Toff024 ∷ []) (lem-comm-push-TOFF124-sw0-L c4) ▸
       at 2 2 (Sw01 ∷ Bx4-013 ∷ []) (lem-comm-push-BOX⟨4·103⟩-sw0-L c4) ▸
       at 1 2 (Sw01 ∷ Toff024 ∷ []) (lem-comm-push-TOFF124-sw0-L c4) ▸
       at 0 2 (Sw01 ∷ CCZ024 ∷ []) (lem-comm-push-CCZ124-sw0-L c4) ▸
       at 1 6 (Bx0-4213 ∷ []) (refl) ▸ done


-- comm push SBOX(1;4;20;3) sw0 L: 7 steps
lem-comm-push-SBOX⟨1·4·20·3⟩-sw0-L : WsL → ⟪ (Sb1-4-20-3 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Sb0-4-21-3 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨1·4·20·3⟩-sw0-L c4 = run b0
  where
  b0 : Chain (Sb1-4-20-3 ∷ Sw01 ∷ []) (Sw01 ∷ Sb0-4-21-3 ∷ [])
  b0 = at 0 1 (Bx1-4203 ∷ Toff302 ∷ Sb1-4-3-0 ∷ Toff302 ∷ Sb⁻1-4-3-0 ∷ []) (refl) ▸
       at 4 2 (Sw01 ∷ Sb⁻1-4-3-0 ∷ []) (sym (c₂ (Swap) ((CS • CS • CS) ↑))) ▸
       at 3 2 (Sw01 ∷ Toff312 ∷ []) (sym (wl0063 c4)) ▸
       at 2 2 (Sw01 ∷ Sb1-4-3-0 ∷ []) (sym (c₂ (Swap) (CS ↑))) ▸
       at 1 2 (Sw01 ∷ Toff312 ∷ []) (sym (wl0063 c4)) ▸
       at 0 2 (Sw01 ∷ Bx0-4213 ∷ []) (lem-comm-push-BOX⟨1·4203⟩-sw0-L c4) ▸
       at 1 5 (Sb0-4-21-3 ∷ []) (refl) ▸ done


-- comm push SBOXd(0;4;3;1) sw2 L: 3 steps
lem-comm-push-SBOXd⟨0·4·3·1⟩-sw2-L : WsL → ⟪ (Sb⁻0-4-3-1 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sb⁻0-4-2-1 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨0·4·3·1⟩-sw2-L c4 = run b0
  where
  b0 : Chain (Sb⁻0-4-3-1 ∷ Sw23 ∷ []) (Sw23 ∷ Sb⁻0-4-2-1 ∷ [])
  b0 = at 0 1 (CS34⁻ ∷ []) (refl) ▸
       at 0 2 (Sw23 ∷ CS24⁻ ∷ []) (wl0009 c4) ▸
       at 1 1 (Sb⁻0-4-2-1 ∷ []) (refl) ▸ done


-- comm push SBOX(0;4;3;1) sw2 L: 3 steps
lem-comm-push-SBOX⟨0·4·3·1⟩-sw2-L : WsL → ⟪ (Sb0-4-3-1 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sb0-4-2-1 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨0·4·3·1⟩-sw2-L c4 = run b0
  where
  b0 : Chain (Sb0-4-3-1 ∷ Sw23 ∷ []) (Sw23 ∷ Sb0-4-2-1 ∷ [])
  b0 = at 0 1 (CS34 ∷ []) (refl) ▸
       at 0 2 (Sw23 ∷ CS24 ∷ []) (wl0008 c4) ▸
       at 1 1 (Sb0-4-2-1 ∷ []) (refl) ▸ done


-- comm push BOX(0;43) sw2 L: 3 steps
lem-comm-push-BOX⟨0·43⟩-sw2-L : WsL → ⟪ (Bx0-43 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Bx0-42 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·43⟩-sw2-L c4 = run b0
  where
  b0 : Chain (Bx0-43 ∷ Sw23 ∷ []) (Sw23 ∷ Bx0-42 ∷ [])
  b0 = at 0 1 (CZ34 ∷ []) (refl) ▸
       at 0 2 (Sw23 ∷ CZ24 ∷ []) (wl0035 c4) ▸
       at 1 1 (Bx0-42 ∷ []) (refl) ▸ done


-- comm push BOX(4;013) sw2 L: 8 steps
lem-comm-push-BOX⟨4·013⟩-sw2-L : WsL → ⟪ (Bx4-013 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Bx4-012 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨4·013⟩-sw2-L c4 = run b0
  where
  b0 : Chain (Bx4-013 ∷ Sw23 ∷ []) (Sw23 ∷ Bx4-012 ∷ [])
  b0 = at 0 1 (CCZ014 ∷ Toff401 ∷ Bx0-43 ∷ Toff401 ∷ CCZ014 ∷ Bx0-43 ∷ []) (refl) ▸
       at 5 2 (Sw23 ∷ Bx0-42 ∷ []) (lem-comm-push-BOX⟨0·43⟩-sw2-L c4) ▸
       at 4 2 (Sw23 ∷ CCZ014 ∷ []) (lem-comm-push-CCZ014-sw2-L c4) ▸
       at 3 2 (Sw23 ∷ Toff401 ∷ []) (lem-comm-push-TOFF401-sw2-L c4) ▸
       at 2 2 (Sw23 ∷ Bx0-42 ∷ []) (lem-comm-push-BOX⟨0·43⟩-sw2-L c4) ▸
       at 1 2 (Sw23 ∷ Toff401 ∷ []) (lem-comm-push-TOFF401-sw2-L c4) ▸
       at 0 2 (Sw23 ∷ CCZ014 ∷ []) (lem-comm-push-CCZ014-sw2-L c4) ▸
       at 1 6 (Bx4-012 ∷ []) (refl) ▸ done


-- comm push BOX(0;4213) sw2 L: 12 steps
lem-comm-push-BOX⟨0·4213⟩-sw2-L : WsL → ⟪ (Bx0-4213 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Bx0-4312 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·4213⟩-sw2-L c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-4213 ∷ Sw23 ∷ []) (CCZ024 ∷ Sw23 ∷ Sw23 ∷ Toff024 ∷ Sw23 ∷ Bx4-012 ∷ Toff034 ∷ CCZ034 ∷ Bx4-012 ∷ [])
  b0 = at 0 1 (CCZ024 ∷ Toff024 ∷ Bx4-013 ∷ Toff024 ∷ CCZ024 ∷ Bx4-013 ∷ []) (refl) ▸
       at 5 2 (Sw23 ∷ Bx4-012 ∷ []) (lem-comm-push-BOX⟨4·013⟩-sw2-L c4) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 5 3 (CCZ034 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (Toff034 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw23 ∷ Bx4-012 ∷ []) (lem-comm-push-BOX⟨4·013⟩-sw2-L c4) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸ done

  b1 : Chain (CCZ024 ∷ Sw23 ∷ Sw23 ∷ Toff024 ∷ Sw23 ∷ Bx4-012 ∷ Toff034 ∷ CCZ034 ∷ Bx4-012 ∷ []) (Sw23 ∷ Bx0-4312 ∷ [])
  b1 = at 2 3 (Toff034 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (CCZ034 ∷ []) (by-assoc Eq.refl) ▸
       at 1 6 (Bx0-4312 ∷ []) (refl) ▸ done


-- comm push SBOX(0;4;21;3) sw2 L: 7 steps
lem-comm-push-SBOX⟨0·4·21·3⟩-sw2-L : WsL → ⟪ (Sb0-4-21-3 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sb0-4-31-2 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨0·4·21·3⟩-sw2-L c4 = run b0
  where
  b0 : Chain (Sb0-4-21-3 ∷ Sw23 ∷ []) (Sw23 ∷ Sb0-4-31-2 ∷ [])
  b0 = at 0 1 (Bx0-4213 ∷ Toff312 ∷ Sb0-4-3-1 ∷ Toff312 ∷ Sb⁻0-4-3-1 ∷ []) (refl) ▸
       at 4 2 (Sw23 ∷ Sb⁻0-4-2-1 ∷ []) (lem-comm-push-SBOXd⟨0·4·3·1⟩-sw2-L c4) ▸
       at 3 2 (Sw23 ∷ Toff213 ∷ []) (sym (wl0126 c4)) ▸
       at 2 2 (Sw23 ∷ Sb0-4-2-1 ∷ []) (lem-comm-push-SBOX⟨0·4·3·1⟩-sw2-L c4) ▸
       at 1 2 (Sw23 ∷ Toff213 ∷ []) (sym (wl0126 c4)) ▸
       at 0 2 (Sw23 ∷ Bx0-4312 ∷ []) (lem-comm-push-BOX⟨0·4213⟩-sw2-L c4) ▸
       at 1 5 (Sb0-4-31-2 ∷ []) (refl) ▸ done


-- comm push SBOXd(0;4;2;1) sw1 L: 3 steps
lem-comm-push-SBOXd⟨0·4·2·1⟩-sw1-L : WsL → ⟪ (Sb⁻0-4-2-1 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sb⁻0-4-1-2 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨0·4·2·1⟩-sw1-L c4 = run b0
  where
  b0 : Chain (Sb⁻0-4-2-1 ∷ Sw12 ∷ []) (Sw12 ∷ Sb⁻0-4-1-2 ∷ [])
  b0 = at 0 1 (CS24⁻ ∷ []) (refl) ▸
       at 0 2 (Sw12 ∷ CS14⁻ ∷ []) (wl0007 c4) ▸
       at 1 1 (Sb⁻0-4-1-2 ∷ []) (refl) ▸ done


-- comm push SBOX(0;4;2;1) sw1 L: 3 steps
lem-comm-push-SBOX⟨0·4·2·1⟩-sw1-L : WsL → ⟪ (Sb0-4-2-1 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sb0-4-1-2 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨0·4·2·1⟩-sw1-L c4 = run b0
  where
  b0 : Chain (Sb0-4-2-1 ∷ Sw12 ∷ []) (Sw12 ∷ Sb0-4-1-2 ∷ [])
  b0 = at 0 1 (CS24 ∷ []) (refl) ▸
       at 0 2 (Sw12 ∷ CS14 ∷ []) (wl0005 c4) ▸
       at 1 1 (Sb0-4-1-2 ∷ []) (refl) ▸ done


-- comm push BOX(0;42) sw1 L: 3 steps
lem-comm-push-BOX⟨0·42⟩-sw1-L : WsL → ⟪ (Bx0-42 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Bx0-41 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·42⟩-sw1-L c4 = run b0
  where
  b0 : Chain (Bx0-42 ∷ Sw12 ∷ []) (Sw12 ∷ Bx0-41 ∷ [])
  b0 = at 0 1 (CZ24 ∷ []) (refl) ▸
       at 0 2 (Sw12 ∷ CZ14 ∷ []) (wl0053 c4) ▸
       at 1 1 (Bx0-41 ∷ []) (refl) ▸ done


-- comm push BOX(4;012) sw1 L: 12 steps
lem-comm-push-BOX⟨4·012⟩-sw1-L : WsL → ⟪ (Bx4-012 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Bx4-021 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨4·012⟩-sw1-L c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx4-012 ∷ Sw12 ∷ []) (CCZ014 ∷ Sw12 ∷ Sw12 ∷ Toff401 ∷ Sw12 ∷ Bx0-41 ∷ Toff402 ∷ CCZ024 ∷ Bx0-41 ∷ [])
  b0 = at 0 1 (CCZ014 ∷ Toff401 ∷ Bx0-42 ∷ Toff401 ∷ CCZ014 ∷ Bx0-42 ∷ []) (refl) ▸
       at 5 2 (Sw12 ∷ Bx0-41 ∷ []) (lem-comm-push-BOX⟨0·42⟩-sw1-L c4) ▸
       at 4 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 5 3 (CCZ024 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 4 3 (Toff402 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw12 ∷ Bx0-41 ∷ []) (lem-comm-push-BOX⟨0·42⟩-sw1-L c4) ▸
       at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸ done

  b1 : Chain (CCZ014 ∷ Sw12 ∷ Sw12 ∷ Toff401 ∷ Sw12 ∷ Bx0-41 ∷ Toff402 ∷ CCZ024 ∷ Bx0-41 ∷ []) (Sw12 ∷ Bx4-021 ∷ [])
  b1 = at 2 3 (Toff402 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 1 3 (CCZ024 ∷ []) (by-assoc Eq.refl) ▸
       at 1 6 (Bx4-021 ∷ []) (refl) ▸ done


-- comm push BOX(0;4312) sw1 L: 8 steps
lem-comm-push-BOX⟨0·4312⟩-sw1-L : WsL → ⟪ (Bx0-4312 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Bx0-4321 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·4312⟩-sw1-L c4 = run b0
  where
  b0 : Chain (Bx0-4312 ∷ Sw12 ∷ []) (Sw12 ∷ Bx0-4321 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff034 ∷ Bx4-012 ∷ Toff034 ∷ CCZ034 ∷ Bx4-012 ∷ []) (refl) ▸
       at 5 2 (Sw12 ∷ Bx4-021 ∷ []) (lem-comm-push-BOX⟨4·012⟩-sw1-L c4) ▸
       at 4 2 (Sw12 ∷ CCZ034 ∷ []) (lem-comm-push-CCZ034-sw1-L c4) ▸
       at 3 2 (Sw12 ∷ Toff034 ∷ []) (lem-comm-push-TOFF034-sw1-L c4) ▸
       at 2 2 (Sw12 ∷ Bx4-021 ∷ []) (lem-comm-push-BOX⟨4·012⟩-sw1-L c4) ▸
       at 1 2 (Sw12 ∷ Toff034 ∷ []) (lem-comm-push-TOFF034-sw1-L c4) ▸
       at 0 2 (Sw12 ∷ CCZ034 ∷ []) (lem-comm-push-CCZ034-sw1-L c4) ▸
       at 1 6 (Bx0-4321 ∷ []) (refl) ▸ done


-- comm push SBOX(0;4;31;2) sw1 L: 7 steps
lem-comm-push-SBOX⟨0·4·31·2⟩-sw1-L : WsL → ⟪ (Sb0-4-31-2 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sb0-4-32-1 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨0·4·31·2⟩-sw1-L c4 = run b0
  where
  b0 : Chain (Sb0-4-31-2 ∷ Sw12 ∷ []) (Sw12 ∷ Sb0-4-32-1 ∷ [])
  b0 = at 0 1 (Bx0-4312 ∷ Toff213 ∷ Sb0-4-2-1 ∷ Toff213 ∷ Sb⁻0-4-2-1 ∷ []) (refl) ▸
       at 4 2 (Sw12 ∷ Sb⁻0-4-1-2 ∷ []) (lem-comm-push-SBOXd⟨0·4·2·1⟩-sw1-L c4) ▸
       at 3 2 (Sw12 ∷ Toff123 ∷ []) (sym (wl0127 c4)) ▸
       at 2 2 (Sw12 ∷ Sb0-4-1-2 ∷ []) (lem-comm-push-SBOX⟨0·4·2·1⟩-sw1-L c4) ▸
       at 1 2 (Sw12 ∷ Toff123 ∷ []) (sym (wl0127 c4)) ▸
       at 0 2 (Sw12 ∷ Bx0-4321 ∷ []) (lem-comm-push-BOX⟨0·4312⟩-sw1-L c4) ▸
       at 1 5 (Sb0-4-32-1 ∷ []) (refl) ▸ done


-- comm push SBOXd(0;4;1;2) sw3 L: 4 steps
lem-comm-push-SBOXd⟨0·4·1·2⟩-sw3-L : WsL → ⟪ (Sb⁻0-4-1-2 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Sw34 ∷ Sb⁻0-3-1-2 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨0·4·1·2⟩-sw3-L c4 = run b0
  where
  b0 : Chain (Sb⁻0-4-1-2 ∷ Sw34 ∷ []) (Sw34 ∷ Sb⁻0-3-1-2 ∷ [])
  b0 = at 0 1 (CS14⁻ ∷ []) (refl) ▸
       at 0 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0004 c4) ▸
       at 1 1 (Sb⁻0-3-1-2 ∷ []) (refl) ▸ done


-- comm push SBOX(0;4;1;2) sw3 L: 4 steps
lem-comm-push-SBOX⟨0·4·1·2⟩-sw3-L : WsL → ⟪ (Sb0-4-1-2 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Sw34 ∷ Sb0-3-1-2 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨0·4·1·2⟩-sw3-L c4 = run b0
  where
  b0 : Chain (Sb0-4-1-2 ∷ Sw34 ∷ []) (Sw34 ∷ Sb0-3-1-2 ∷ [])
  b0 = at 0 1 (CS14 ∷ []) (refl) ▸
       at 0 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0004 c4) ▸
       at 1 1 (Sb0-3-1-2 ∷ []) (refl) ▸ done


-- comm push BOX(0;41) sw3 L: 4 steps
lem-comm-push-BOX⟨0·41⟩-sw3-L : WsL → ⟪ (Bx0-41 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Sw34 ∷ Bx0-31 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·41⟩-sw3-L c4 = run b0
  where
  b0 : Chain (Bx0-41 ∷ Sw34 ∷ []) (Sw34 ∷ Bx0-31 ∷ [])
  b0 = at 0 1 (CZ14 ∷ []) (refl) ▸
       at 0 1 (Sw34 ∷ CZ13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0004 c4) ▸
       at 1 1 (Bx0-31 ∷ []) (refl) ▸ done


-- comm push BOX(4;021) sw3 L: 8 steps
lem-comm-push-BOX⟨4·021⟩-sw3-L : WsL → ⟪ (Bx4-021 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Sw34 ∷ Bx3-021 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨4·021⟩-sw3-L c4 = run b0
  where
  b0 : Chain (Bx4-021 ∷ Sw34 ∷ []) (Sw34 ∷ Bx3-021 ∷ [])
  b0 = at 0 1 (CCZ024 ∷ Toff402 ∷ Bx0-41 ∷ Toff402 ∷ CCZ024 ∷ Bx0-41 ∷ []) (refl) ▸
       at 5 2 (Sw34 ∷ Bx0-31 ∷ []) (lem-comm-push-BOX⟨0·41⟩-sw3-L c4) ▸
       at 4 2 (Sw34 ∷ CCZ023 ∷ []) (lem-comm-push-CCZ024-sw3-L c4) ▸
       at 3 2 (Sw34 ∷ Toff302 ∷ []) (lem-comm-push-TOFF402-sw3-L c4) ▸
       at 2 2 (Sw34 ∷ Bx0-31 ∷ []) (lem-comm-push-BOX⟨0·41⟩-sw3-L c4) ▸
       at 1 2 (Sw34 ∷ Toff302 ∷ []) (lem-comm-push-TOFF402-sw3-L c4) ▸
       at 0 2 (Sw34 ∷ CCZ023 ∷ []) (lem-comm-push-CCZ024-sw3-L c4) ▸
       at 1 6 (Bx3-021 ∷ []) (refl) ▸ done


-- comm push CX04 sw2 R: 7 steps
lem-comm-push-CX04-sw2-R : WsL → ⟪ (Sw23 ∷ CX04 ∷ []) ⟫ʷ ≈ ⟪ (CX04 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-CX04-sw2-R c4 = run b0
  where
  b0 : Chain (Sw23 ∷ CX04 ∷ []) (CX04 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0002 c4) ▸
       at 2 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 3 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 4 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 5 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (sym (wl0002 c4)) ▸
       at 0 7 (CX04 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm push CX04 sw1 R: 5 steps
lem-comm-push-CX04-sw1-R : WsL → ⟪ (Sw12 ∷ CX04 ∷ []) ⟫ʷ ≈ ⟪ (CX04 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-CX04-sw1-R c4 = run b0
  where
  b0 : Chain (Sw12 ∷ CX04 ∷ []) (CX04 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 1 2 (CX03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸
       at 2 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 0 3 (CX04 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm push CCZ034 sw3 L: 87 steps
lem-comm-push-CCZ034-sw3-L : WsL → ⟪ (CCZ034 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Sw34 ∷ CCZ034 ∷ []) ⟫ʷ
lem-comm-push-CCZ034-sw3-L c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (run b10))))))))))
  where
  b0 : Chain (CCZ034 ∷ Sw34 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 0 1 (Sw23 ∷ CCZ024 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw12 ∷ CCZ014 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ CCZ013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw12 ∷ CS14 ∷ Sw34 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ [])
  b1 = at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0003 c4) ▸
       at 4 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw23 ∷ Sw12 ∷ CS14 ∷ Sw34 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ [])
  b2 = at 3 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 4 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0004 c4) ▸
       at 1 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0005 c4)) ▸ done

  b3 : Chain (Sw23 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (CS34 ∷ Sw23 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ Sw23 ∷ Sw34 ∷ [])
  b3 = at 4 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 2 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS24⁻ ∷ Sw12 ∷ []) (sym (wl0007 c4)) ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R c4) ▸
       at 6 2 [] (wl0006 c4) ▸
       at 0 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0008 c4)) ▸ done

  b4 : Chain (CS34 ∷ Sw23 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ Sw23 ∷ Sw34 ∷ []) (CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw34 ∷ [])
  b4 = at 3 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0009 c4)) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 3 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS04 ∷ Sw23 ∷ []) (lem-comm-push-CS04-sw2-R c4) ▸
       at 5 2 [] (wl0003 c4) ▸
       at 4 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b5 : Chain (CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw34 ∷ []) (Sw34 ∷ Sw23 ∷ Sw23 ∷ CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ [])
  b5 = at 6 2 [] (wl0004 c4) ▸
       at 3 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 4 3 (CX04 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw34 ∷ CS34⁻ ∷ []) (wl0128 c4) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 3 (CX04 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw34 ∷ CS34 ∷ []) (wl0129 c4) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸ done

  b6 : Chain (Sw34 ∷ Sw23 ∷ Sw23 ∷ CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ []) (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS14 ∷ Sw12 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ Sw23 ∷ [])
  b6 = at 2 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0011 c4)) ▸
       at 3 2 (CX04 ∷ Sw23 ∷ []) (lem-comm-push-CX04-sw2-R c4) ▸
       at 4 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0012 c4)) ▸
       at 5 2 (CX04 ∷ Sw23 ∷ []) (lem-comm-push-CX04-sw2-R c4) ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0003 c4) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 3 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 c4)) ▸ done

  b7 : Chain (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS14 ∷ Sw12 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ [])
  b7 = at 4 2 (CX04 ∷ Sw12 ∷ []) (lem-comm-push-CX04-sw1-R c4) ▸
       at 5 2 (CS14⁻ ∷ Sw12 ∷ []) (sym (wl0014 c4)) ▸
       at 6 2 (CX04 ∷ Sw12 ∷ []) (lem-comm-push-CX04-sw1-R c4) ▸
       at 8 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0006 c4) ▸
       at 3 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 5 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0004 c4) ▸ done

  b8 : Chain (Sw34 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Sw23 ∷ CS13 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b8 = at 6 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0004 c4) ▸
       at 7 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0004 c4) ▸
       at 8 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0004 c4) ▸
       at 8 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸ done

  b9 : Chain (Sw34 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Sw23 ∷ CS13 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ Sw23 ∷ CS01 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b9 = at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0003 c4) ▸
       at 7 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0003 c4) ▸
       at 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0003 c4) ▸
       at 9 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0003 c4) ▸ done

  b10 : Chain (Sw34 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ Sw23 ∷ CS01 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Sw34 ∷ CCZ034 ∷ [])
  b10 = at 9 2 (CS01 ∷ Sw23 ∷ []) (sym (c₂ (CS) (Swap))) ▸
       at 5 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (sym (wl0130 c4)) ▸
       at 5 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 4 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (CCZ014 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (CCZ024 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (CCZ034 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm push TOFF034 sw3 L: 114 steps
lem-comm-push-TOFF034-sw3-L : WsL → ⟪ (Toff034 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Sw34 ∷ Toff034 ∷ []) ⟫ʷ
lem-comm-push-TOFF034-sw3-L c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (run b14))))))))))))))
  where
  b0 : Chain (Toff034 ∷ Sw34 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Toff024 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw12 ∷ Toff014 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ [])
  b1 = at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 10 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸ done

  b2 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ [])
  b2 = at 11 2 [] (wl0003 c4) ▸
       at 2 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 5 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸ done

  b3 : Chain (Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ K0 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ [])
  b3 = at 9 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 7 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 9 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 10 2 [] (wl0004 c4) ▸
       at 1 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 2 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0005 c4)) ▸
       at 5 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸ done

  b4 : Chain (Sw23 ∷ K0 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ [])
  b4 = at 3 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS24⁻ ∷ Sw12 ∷ []) (sym (wl0007 c4)) ▸
       at 7 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 5 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R c4) ▸
       at 7 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 8 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 9 2 [] (wl0006 c4) ▸ done

  b5 : Chain (Sw23 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ []) (K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ [])
  b5 = at 0 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 1 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0008 c4)) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 2 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0009 c4)) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS04 ∷ Sw23 ∷ []) (lem-comm-push-CS04-sw2-R c4) ▸ done

  b6 : Chain (K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ []) (K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ Sw34 ∷ Sw34 ∷ CX03 ∷ Sw34 ∷ CS03 ∷ K0 ∷ ι ∷ [])
  b6 = at 6 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 7 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 8 2 [] (wl0003 c4) ▸
       at 7 2 (Sw34 ∷ ι ∷ []) (c₁ (iI) (Swap ↑ ↑)) ▸
       at 6 2 (Sw34 ∷ K0 ∷ []) (c₁ (K) (Swap ↑ ↑)) ▸
       at 5 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0004 c4) ▸
       at 4 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸ done

  b7 : Chain (K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ Sw34 ∷ Sw34 ∷ CX03 ∷ Sw34 ∷ CS03 ∷ K0 ∷ ι ∷ []) (Sw34 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ K0 ∷ ι ∷ [])
  b7 = at 5 3 (CX04 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw34 ∷ CS34⁻ ∷ []) (wl0128 c4) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (CX04 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw34 ∷ CS34 ∷ []) (wl0129 c4) ▸
       at 0 2 (Sw34 ∷ K0 ∷ []) (c₁ (K) (Swap ↑ ↑)) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 2 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸ done

  b8 : Chain (Sw34 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ K0 ∷ ι ∷ []) (Sw34 ∷ Sw23 ∷ K0 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ [])
  b8 = at 3 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0011 c4)) ▸
       at 4 2 (CX04 ∷ Sw23 ∷ []) (lem-comm-push-CX04-sw2-R c4) ▸
       at 5 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0012 c4)) ▸
       at 6 2 (CX04 ∷ Sw23 ∷ []) (lem-comm-push-CX04-sw2-R c4) ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0003 c4) ▸
       at 8 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸ done

  b9 : Chain (Sw34 ∷ Sw23 ∷ K0 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ Sw12 ∷ K0 ∷ ι ∷ Sw23 ∷ [])
  b9 = at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 3 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 4 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 c4)) ▸
       at 5 2 (CX04 ∷ Sw12 ∷ []) (lem-comm-push-CX04-sw1-R c4) ▸
       at 6 2 (CS14⁻ ∷ Sw12 ∷ []) (sym (wl0014 c4)) ▸
       at 7 2 (CX04 ∷ Sw12 ∷ []) (lem-comm-push-CX04-sw1-R c4) ▸
       at 9 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0006 c4) ▸ done

  b10 : Chain (Sw34 ∷ Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ Sw12 ∷ K0 ∷ ι ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX03 ∷ Sw34 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ [])
  b10 = at 9 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 10 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 3 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 4 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 6 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0004 c4) ▸
       at 7 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0004 c4) ▸ done

  b11 : Chain (Sw34 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX03 ∷ Sw34 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ CS13 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b11 = at 8 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0004 c4) ▸
       at 9 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0004 c4) ▸
       at 9 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 10 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 11 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸ done

  b12 : Chain (Sw34 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ CS13 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX02 ∷ Sw23 ∷ CS01 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b12 = at 5 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0003 c4) ▸
       at 8 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0003 c4) ▸
       at 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0003 c4) ▸
       at 10 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b13 : Chain (Sw34 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX02 ∷ Sw23 ∷ CS01 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw12 ∷ Toff014 ∷ Sw12 ∷ Sw23 ∷ [])
  b13 = at 9 2 [] (wl0003 c4) ▸
       at 10 2 (CS01 ∷ Sw23 ∷ []) (sym (c₂ (CS) (Swap))) ▸
       at 11 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 12 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 5 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (sym (wl0131 c4)) ▸
       at 5 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 4 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (Toff014 ∷ []) (by-assoc Eq.refl) ▸ done

  b14 : Chain (Sw34 ∷ Sw23 ∷ Sw12 ∷ Toff014 ∷ Sw12 ∷ Sw23 ∷ []) (Sw34 ∷ Toff034 ∷ [])
  b14 = at 2 3 (Toff024 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff034 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm push BOX(0;4321) sw3 L: 8 steps
lem-comm-push-BOX⟨0·4321⟩-sw3-L : WsL → ⟪ (Bx0-4321 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Sw34 ∷ Bx0-3421 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·4321⟩-sw3-L c4 = run b0
  where
  b0 : Chain (Bx0-4321 ∷ Sw34 ∷ []) (Sw34 ∷ Bx0-3421 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff034 ∷ Bx4-021 ∷ Toff034 ∷ CCZ034 ∷ Bx4-021 ∷ []) (refl) ▸
       at 5 2 (Sw34 ∷ Bx3-021 ∷ []) (lem-comm-push-BOX⟨4·021⟩-sw3-L c4) ▸
       at 4 2 (Sw34 ∷ CCZ034 ∷ []) (lem-comm-push-CCZ034-sw3-L c4) ▸
       at 3 2 (Sw34 ∷ Toff034 ∷ []) (lem-comm-push-TOFF034-sw3-L c4) ▸
       at 2 2 (Sw34 ∷ Bx3-021 ∷ []) (lem-comm-push-BOX⟨4·021⟩-sw3-L c4) ▸
       at 1 2 (Sw34 ∷ Toff034 ∷ []) (lem-comm-push-TOFF034-sw3-L c4) ▸
       at 0 2 (Sw34 ∷ CCZ034 ∷ []) (lem-comm-push-CCZ034-sw3-L c4) ▸
       at 1 6 (Bx0-3421 ∷ []) (refl) ▸ done


-- comm push SBOX(0;4;32;1) sw3 L: 9 steps
lem-comm-push-SBOX⟨0·4·32·1⟩-sw3-L : WsL → ⟪ (Sb0-4-32-1 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Sw34 ∷ Sb0-3-42-1 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨0·4·32·1⟩-sw3-L c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-4-32-1 ∷ Sw34 ∷ []) (Sw34 ∷ Bx0-3421 ∷ Toff124 ∷ Sb0-3-1-2 ∷ Toff124 ∷ Sb⁻0-3-1-2 ∷ [])
  b0 = at 0 1 (Bx0-4321 ∷ Toff123 ∷ Sb0-4-1-2 ∷ Toff123 ∷ Sb⁻0-4-1-2 ∷ []) (refl) ▸
       at 4 2 (Sw34 ∷ Sb⁻0-3-1-2 ∷ []) (lem-comm-push-SBOXd⟨0·4·1·2⟩-sw3-L c4) ▸
       at 3 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 4 3 (Toff124 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw34 ∷ Sb0-3-1-2 ∷ []) (lem-comm-push-SBOX⟨0·4·1·2⟩-sw3-L c4) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 3 (Toff124 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw34 ∷ Bx0-3421 ∷ []) (lem-comm-push-BOX⟨0·4321⟩-sw3-L c4) ▸ done

  b1 : Chain (Sw34 ∷ Bx0-3421 ∷ Toff124 ∷ Sb0-3-1-2 ∷ Toff124 ∷ Sb⁻0-3-1-2 ∷ []) (Sw34 ∷ Sb0-3-42-1 ∷ [])
  b1 = at 1 5 (Sb0-3-42-1 ∷ []) (refl) ▸ done


-- comm push SBOXd(0;3;1;2) sw2 L: 4 steps
lem-comm-push-SBOXd⟨0·3·1·2⟩-sw2-L : WsL → ⟪ (Sb⁻0-3-1-2 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sb⁻0-2-1-3 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨0·3·1·2⟩-sw2-L c4 = run b0
  where
  b0 : Chain (Sb⁻0-3-1-2 ∷ Sw23 ∷ []) (Sw23 ∷ Sb⁻0-2-1-3 ∷ [])
  b0 = at 0 1 (CS13⁻ ∷ []) (refl) ▸
       at 0 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0003 c4) ▸
       at 1 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸ done


-- comm push SBOX(0;3;1;2) sw2 L: 4 steps
lem-comm-push-SBOX⟨0·3·1·2⟩-sw2-L : WsL → ⟪ (Sb0-3-1-2 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sb0-2-1-3 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨0·3·1·2⟩-sw2-L c4 = run b0
  where
  b0 : Chain (Sb0-3-1-2 ∷ Sw23 ∷ []) (Sw23 ∷ Sb0-2-1-3 ∷ [])
  b0 = at 0 1 (CS13 ∷ []) (refl) ▸
       at 0 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0003 c4) ▸
       at 1 1 (Sb0-2-1-3 ∷ []) (refl) ▸ done


-- comm push BOX(0;31) sw2 L: 4 steps
lem-comm-push-BOX⟨0·31⟩-sw2-L : WsL → ⟪ (Bx0-31 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Bx0-21 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·31⟩-sw2-L c4 = run b0
  where
  b0 : Chain (Bx0-31 ∷ Sw23 ∷ []) (Sw23 ∷ Bx0-21 ∷ [])
  b0 = at 0 1 (CZ13 ∷ []) (refl) ▸
       at 0 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0003 c4) ▸
       at 1 1 (Bx0-21 ∷ []) (refl) ▸ done


-- comm push BOX(3;021) sw2 L: 8 steps
lem-comm-push-BOX⟨3·021⟩-sw2-L : WsL → ⟪ (Bx3-021 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Bx2-031 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨3·021⟩-sw2-L c4 = run b0
  where
  b0 : Chain (Bx3-021 ∷ Sw23 ∷ []) (Sw23 ∷ Bx2-031 ∷ [])
  b0 = at 0 1 (CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Toff302 ∷ CCZ023 ∷ Bx0-31 ∷ []) (refl) ▸
       at 5 2 (Sw23 ∷ Bx0-21 ∷ []) (lem-comm-push-BOX⟨0·31⟩-sw2-L c4) ▸
       at 4 2 (Sw23 ∷ CCZ023 ∷ []) (wl0132 c4) ▸
       at 3 2 (Sw23 ∷ Toff203 ∷ []) (sym (wl0133 c4)) ▸
       at 2 2 (Sw23 ∷ Bx0-21 ∷ []) (lem-comm-push-BOX⟨0·31⟩-sw2-L c4) ▸
       at 1 2 (Sw23 ∷ Toff203 ∷ []) (sym (wl0133 c4)) ▸
       at 0 2 (Sw23 ∷ CCZ023 ∷ []) (wl0132 c4) ▸
       at 1 6 (Bx2-031 ∷ []) (refl) ▸ done


-- comm push BOX(0;3421) sw2 L: 12 steps
lem-comm-push-BOX⟨0·3421⟩-sw2-L : WsL → ⟪ (Bx0-3421 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Bx0-2431 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·3421⟩-sw2-L c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-3421 ∷ Sw23 ∷ []) (CCZ034 ∷ Sw23 ∷ Toff024 ∷ Sw23 ∷ Sw23 ∷ Bx2-031 ∷ Toff024 ∷ CCZ024 ∷ Bx2-031 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff034 ∷ Bx3-021 ∷ Toff034 ∷ CCZ034 ∷ Bx3-021 ∷ []) (refl) ▸
       at 5 2 (Sw23 ∷ Bx2-031 ∷ []) (lem-comm-push-BOX⟨3·021⟩-sw2-L c4) ▸
       at 4 1 (Sw23 ∷ CCZ024 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0003 c4) ▸
       at 3 1 (Sw23 ∷ Toff024 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0003 c4) ▸
       at 2 2 (Sw23 ∷ Bx2-031 ∷ []) (lem-comm-push-BOX⟨3·021⟩-sw2-L c4) ▸
       at 1 1 (Sw23 ∷ Toff024 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (CCZ034 ∷ Sw23 ∷ Toff024 ∷ Sw23 ∷ Sw23 ∷ Bx2-031 ∷ Toff024 ∷ CCZ024 ∷ Bx2-031 ∷ []) (Sw23 ∷ Bx0-2431 ∷ [])
  b1 = at 3 2 [] (wl0003 c4) ▸
       at 0 1 (Sw23 ∷ CCZ024 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0003 c4) ▸
       at 1 6 (Bx0-2431 ∷ []) (refl) ▸ done


-- comm push SBOX(0;3;42;1) sw2 L: 9 steps
lem-comm-push-SBOX⟨0·3·42·1⟩-sw2-L : WsL → ⟪ (Sb0-3-42-1 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨0·3·42·1⟩-sw2-L c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-3-42-1 ∷ Sw23 ∷ []) (Sw23 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b0 = at 0 1 (Bx0-3421 ∷ Toff124 ∷ Sb0-3-1-2 ∷ Toff124 ∷ Sb⁻0-3-1-2 ∷ []) (refl) ▸
       at 4 2 (Sw23 ∷ Sb⁻0-2-1-3 ∷ []) (lem-comm-push-SBOXd⟨0·3·1·2⟩-sw2-L c4) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (Toff134 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw23 ∷ Sb0-2-1-3 ∷ []) (lem-comm-push-SBOX⟨0·3·1·2⟩-sw2-L c4) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 2 3 (Toff134 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ Bx0-2431 ∷ []) (lem-comm-push-BOX⟨0·3421⟩-sw2-L c4) ▸ done

  b1 : Chain (Sw23 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Sw23 ∷ Sb0-2-43-1 ∷ [])
  b1 = at 1 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done


-- comm push BOX(0;21) sw2 R: 4 steps
lem-comm-push-BOX⟨0·21⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Bx0-21 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-31 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·21⟩-sw2-R c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-21 ∷ []) (Bx0-31 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ12 ∷ []) (refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 0 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸
       at 0 1 (Bx0-31 ∷ []) (refl) ▸ done


-- comm push BOX(2;031) sw2 R: 8 steps
lem-comm-push-BOX⟨2·031⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Bx2-031 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-021 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨2·031⟩-sw2-R c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-031 ∷ []) (Bx3-021 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw23 ∷ []) (sym (wl0132 c4)) ▸
       at 1 2 (Toff302 ∷ Sw23 ∷ []) (wl0133 c4) ▸
       at 2 2 (Bx0-31 ∷ Sw23 ∷ []) (lem-comm-push-BOX⟨0·21⟩-sw2-R c4) ▸
       at 3 2 (Toff302 ∷ Sw23 ∷ []) (wl0133 c4) ▸
       at 4 2 (CCZ023 ∷ Sw23 ∷ []) (sym (wl0132 c4)) ▸
       at 5 2 (Bx0-31 ∷ Sw23 ∷ []) (lem-comm-push-BOX⟨0·21⟩-sw2-R c4) ▸
       at 0 6 (Bx3-021 ∷ []) (refl) ▸ done


-- comm push BOX(0;2431) sw2 R: 12 steps
lem-comm-push-BOX⟨0·2431⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3421 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·2431⟩-sw2-R c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw23 ∷ Bx0-2431 ∷ []) (CCZ034 ∷ Toff034 ∷ Bx3-021 ∷ Toff034 ∷ Sw23 ∷ CCZ024 ∷ Bx2-031 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx2-031 ∷ Toff024 ∷ CCZ024 ∷ Bx2-031 ∷ []) (refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 0 3 (CCZ034 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (Toff034 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Bx3-021 ∷ Sw23 ∷ []) (lem-comm-push-BOX⟨2·031⟩-sw2-R c4) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 3 3 (Toff034 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff034 ∷ Bx3-021 ∷ Toff034 ∷ Sw23 ∷ CCZ024 ∷ Bx2-031 ∷ []) (Bx0-3421 ∷ Sw23 ∷ [])
  b1 = at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (CCZ034 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Bx3-021 ∷ Sw23 ∷ []) (lem-comm-push-BOX⟨2·031⟩-sw2-R c4) ▸
       at 0 6 (Bx0-3421 ∷ []) (refl) ▸ done


-- comm push SBOX(0;2;1;3) sw2 R: 4 steps
lem-comm-push-SBOX⟨0·2·1·3⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Sb0-2-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-3-1-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨0·2·1·3⟩-sw2-R c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb0-2-1-3 ∷ []) (Sb0-3-1-2 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS12 ∷ []) (refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 0 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 0 1 (Sb0-3-1-2 ∷ []) (refl) ▸ done


-- comm push SBOXd(0;2;1;3) sw2 R: 4 steps
lem-comm-push-SBOXd⟨0·2·1·3⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Sb⁻0-2-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-3-1-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨0·2·1·3⟩-sw2-R c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻0-2-1-3 ∷ []) (Sb⁻0-3-1-2 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS12⁻ ∷ []) (refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 0 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 0 1 (Sb⁻0-3-1-2 ∷ []) (refl) ▸ done


-- comm push SBOX(0;2;43;1) sw2 R: 9 steps
lem-comm-push-SBOX⟨0·2·43·1⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-3-42-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨0·2·43·1⟩-sw2-R c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw23 ∷ Sb0-2-43-1 ∷ []) (Bx0-3421 ∷ Toff124 ∷ Sb0-3-1-2 ∷ Toff124 ∷ Sb⁻0-3-1-2 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 0 2 (Bx0-3421 ∷ Sw23 ∷ []) (lem-comm-push-BOX⟨0·2431⟩-sw2-R c4) ▸
       at 2 1 (Sw23 ∷ Toff124 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0003 c4) ▸
       at 2 2 (Sb0-3-1-2 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·2·1·3⟩-sw2-R c4) ▸
       at 4 1 (Sw23 ∷ Toff124 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0003 c4) ▸
       at 4 2 (Sb⁻0-3-1-2 ∷ Sw23 ∷ []) (lem-comm-push-SBOXd⟨0·2·1·3⟩-sw2-R c4) ▸ done

  b1 : Chain (Bx0-3421 ∷ Toff124 ∷ Sb0-3-1-2 ∷ Toff124 ∷ Sb⁻0-3-1-2 ∷ Sw23 ∷ []) (Sb0-3-42-1 ∷ Sw23 ∷ [])
  b1 = at 0 5 (Sb0-3-42-1 ∷ []) (refl) ▸ done


-- comm push CCZ034 sw3 R: 87 steps
lem-comm-push-CCZ034-sw3-R : WsL → ⟪ (Sw34 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Sw34 ∷ []) ⟫ʷ
lem-comm-push-CCZ034-sw3-R c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (run b10))))))))))
  where
  b0 : Chain (Sw34 ∷ CCZ034 ∷ []) (Sw34 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CCZ024 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw12 ∷ CCZ014 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ CCZ013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS14 ∷ Sw34 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b1 = at 8 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (wl0003 c4) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS14 ∷ Sw34 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw12 ∷ Sw23 ∷ [])
  b2 = at 4 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 5 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 9 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 7 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0004 c4) ▸
       at 2 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0005 c4)) ▸ done

  b3 : Chain (Sw34 ∷ Sw23 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw12 ∷ Sw23 ∷ []) (Sw34 ∷ CS34 ∷ Sw23 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ Sw23 ∷ [])
  b3 = at 5 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 3 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS24⁻ ∷ Sw12 ∷ []) (sym (wl0007 c4)) ▸
       at 7 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 5 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R c4) ▸
       at 7 2 [] (wl0006 c4) ▸
       at 1 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0008 c4)) ▸ done

  b4 : Chain (Sw34 ∷ CS34 ∷ Sw23 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ Sw23 ∷ []) (CS34 ∷ Sw34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ [])
  b4 = at 4 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 2 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0009 c4)) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS04 ∷ Sw23 ∷ []) (lem-comm-push-CS04-sw2-R c4) ▸
       at 6 2 [] (wl0003 c4) ▸
       at 0 2 (CS34 ∷ Sw34 ∷ []) (sym (wl0129 c4)) ▸ done

  b5 : Chain (CS34 ∷ Sw34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ []) (Sw23 ∷ Sw23 ∷ CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ Sw34 ∷ [])
  b5 = at 3 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 3 (CX04 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CS34⁻ ∷ Sw34 ∷ []) (sym (wl0128 c4)) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (CX04 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0004 c4) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸ done

  b6 : Chain (Sw23 ∷ Sw23 ∷ CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ Sw34 ∷ []) (Sw23 ∷ Sw12 ∷ CS14 ∷ Sw12 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ Sw23 ∷ Sw34 ∷ [])
  b6 = at 1 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0011 c4)) ▸
       at 2 2 (CX04 ∷ Sw23 ∷ []) (lem-comm-push-CX04-sw2-R c4) ▸
       at 3 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0012 c4)) ▸
       at 4 2 (CX04 ∷ Sw23 ∷ []) (lem-comm-push-CX04-sw2-R c4) ▸
       at 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0003 c4) ▸
       at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 2 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 c4)) ▸ done

  b7 : Chain (Sw23 ∷ Sw12 ∷ CS14 ∷ Sw12 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ [])
  b7 = at 3 2 (CX04 ∷ Sw12 ∷ []) (lem-comm-push-CX04-sw1-R c4) ▸
       at 4 2 (CS14⁻ ∷ Sw12 ∷ []) (sym (wl0014 c4)) ▸
       at 5 2 (CX04 ∷ Sw12 ∷ []) (lem-comm-push-CX04-sw1-R c4) ▸
       at 7 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0006 c4) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 4 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0004 c4) ▸ done

  b8 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Sw23 ∷ CS13 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ [])
  b8 = at 5 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0004 c4) ▸
       at 6 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0004 c4) ▸
       at 7 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0004 c4) ▸
       at 7 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸ done

  b9 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Sw23 ∷ CS13 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ Sw23 ∷ CS01 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ [])
  b9 = at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0003 c4) ▸
       at 6 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0003 c4) ▸
       at 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0003 c4) ▸
       at 8 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0003 c4) ▸ done

  b10 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ Sw23 ∷ CS01 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (CCZ034 ∷ Sw34 ∷ [])
  b10 = at 8 2 (CS01 ∷ Sw23 ∷ []) (sym (c₂ (CS) (Swap))) ▸
       at 4 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (sym (wl0130 c4)) ▸
       at 4 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (CCZ014 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (CCZ024 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (CCZ034 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm push TOFF034 sw3 R: 114 steps
lem-comm-push-TOFF034-sw3-R : WsL → ⟪ (Sw34 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Sw34 ∷ []) ⟫ʷ
lem-comm-push-TOFF034-sw3-R c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (run b14))))))))))))))
  where
  b0 : Chain (Sw34 ∷ Toff034 ∷ []) (Sw34 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Toff024 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw12 ∷ Toff014 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b1 = at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 7 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 11 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸ done

  b2 : Chain (Sw34 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b2 = at 12 2 [] (wl0003 c4) ▸
       at 3 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 4 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 6 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸ done

  b3 : Chain (Sw34 ∷ Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ K0 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ [])
  b3 = at 10 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 8 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 10 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 11 2 [] (wl0004 c4) ▸
       at 2 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 3 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0005 c4)) ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸ done

  b4 : Chain (Sw34 ∷ Sw23 ∷ K0 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0 ∷ ι ∷ Sw23 ∷ [])
  b4 = at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS24⁻ ∷ Sw12 ∷ []) (sym (wl0007 c4)) ▸
       at 8 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 6 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R c4) ▸
       at 8 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 9 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 10 2 [] (wl0006 c4) ▸ done

  b5 : Chain (Sw34 ∷ Sw23 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0 ∷ ι ∷ Sw23 ∷ []) (Sw34 ∷ K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw23 ∷ [])
  b5 = at 1 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 2 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0008 c4)) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 3 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0009 c4)) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 5 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS04 ∷ Sw23 ∷ []) (lem-comm-push-CS04-sw2-R c4) ▸ done

  b6 : Chain (Sw34 ∷ K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw23 ∷ []) (K0 ∷ CS34 ∷ CX04 ∷ CS34⁻ ∷ Sw34 ∷ CX03 ∷ CS04 ∷ K0 ∷ ι ∷ [])
  b6 = at 7 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 9 2 [] (wl0003 c4) ▸
       at 0 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 1 2 (CS34 ∷ Sw34 ∷ []) (sym (wl0129 c4)) ▸
       at 4 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 3 (CX04 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS34⁻ ∷ Sw34 ∷ []) (sym (wl0128 c4)) ▸ done

  b7 : Chain (K0 ∷ CS34 ∷ CX04 ∷ CS34⁻ ∷ Sw34 ∷ CX03 ∷ CS04 ∷ K0 ∷ ι ∷ []) (Sw23 ∷ K0 ∷ Sw23 ∷ CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ [])
  b7 = at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 4 3 (CX04 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0004 c4) ▸
       at 6 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 7 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸ done

  b8 : Chain (Sw23 ∷ K0 ∷ Sw23 ∷ CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ []) (Sw23 ∷ K0 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ [])
  b8 = at 2 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0011 c4)) ▸
       at 3 2 (CX04 ∷ Sw23 ∷ []) (lem-comm-push-CX04-sw2-R c4) ▸
       at 4 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0012 c4)) ▸
       at 5 2 (CX04 ∷ Sw23 ∷ []) (lem-comm-push-CX04-sw2-R c4) ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0003 c4) ▸
       at 7 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸ done

  b9 : Chain (Sw23 ∷ K0 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ Sw12 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ [])
  b9 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 2 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 3 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 c4)) ▸
       at 4 2 (CX04 ∷ Sw12 ∷ []) (lem-comm-push-CX04-sw1-R c4) ▸
       at 5 2 (CS14⁻ ∷ Sw12 ∷ []) (sym (wl0014 c4)) ▸
       at 6 2 (CX04 ∷ Sw12 ∷ []) (lem-comm-push-CX04-sw1-R c4) ▸
       at 8 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0006 c4) ▸ done

  b10 : Chain (Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ Sw12 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX03 ∷ Sw34 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ [])
  b10 = at 8 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 9 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 5 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0004 c4) ▸
       at 6 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0004 c4) ▸ done

  b11 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX03 ∷ Sw34 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ CS13 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ [])
  b11 = at 7 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0004 c4) ▸
       at 8 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0004 c4) ▸
       at 8 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 9 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 10 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸ done

  b12 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ CS13 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX02 ∷ Sw23 ∷ CS01 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ [])
  b12 = at 4 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0003 c4) ▸
       at 7 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0003 c4) ▸
       at 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0003 c4) ▸
       at 9 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b13 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX02 ∷ Sw23 ∷ CS01 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw12 ∷ Toff014 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ [])
  b13 = at 8 2 [] (wl0003 c4) ▸
       at 9 2 (CS01 ∷ Sw23 ∷ []) (sym (c₂ (CS) (Swap))) ▸
       at 10 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 11 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 4 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (sym (wl0131 c4)) ▸
       at 4 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff014 ∷ []) (by-assoc Eq.refl) ▸ done

  b14 : Chain (Sw23 ∷ Sw12 ∷ Toff014 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (Toff034 ∷ Sw34 ∷ [])
  b14 = at 1 3 (Toff024 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff034 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm push CCZ023 sw3 R: 58 steps
lem-comm-push-CCZ023-sw3-R : WsL → ⟪ (Sw34 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Sw34 ∷ []) ⟫ʷ
lem-comm-push-CCZ023-sw3-R c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (Sw34 ∷ CCZ023 ∷ []) (Sw34 ∷ Sw12 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw12 ∷ CCZ013 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw34 ∷ Sw12 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw12 ∷ []) (Sw34 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw12 ∷ CX01 ∷ CS03 ∷ Sw12 ∷ [])
  b1 = at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0003 c4) ▸
       at 1 2 (CS23 ∷ Sw12 ∷ []) (sym (wl0047 c4)) ▸
       at 4 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 2 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS23⁻ ∷ Sw12 ∷ []) (sym (wl0029 c4)) ▸ done

  b2 : Chain (Sw34 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw12 ∷ CX01 ∷ CS03 ∷ Sw12 ∷ []) (CS24 ∷ CX02 ∷ Sw34 ∷ CS23⁻ ∷ Sw34 ∷ Sw34 ∷ CX02 ∷ CS03 ∷ [])
  b2 = at 6 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 6 2 [] (wl0006 c4) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 0 3 (CS24 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (CX02 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap))) ▸
       at 4 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸ done

  b3 : Chain (CS24 ∷ CX02 ∷ Sw34 ∷ CS23⁻ ∷ Sw34 ∷ Sw34 ∷ CX02 ∷ CS03 ∷ []) (Sw12 ∷ CS14 ∷ CX01 ∷ Sw12 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ Sw34 ∷ [])
  b3 = at 2 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX02 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap))) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 4 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 1 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 c4)) ▸
       at 3 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0006 c4) ▸ done

  b4 : Chain (Sw12 ∷ CS14 ∷ CX01 ∷ Sw12 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ Sw34 ∷ []) (Sw12 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ Sw34 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw12 ∷ Sw34 ∷ [])
  b4 = at 3 2 (CS14⁻ ∷ Sw12 ∷ []) (sym (wl0014 c4)) ▸
       at 5 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0006 c4) ▸
       at 5 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R c4) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0004 c4) ▸
       at 3 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸ done

  b5 : Chain (Sw12 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ Sw34 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw12 ∷ Sw34 ∷ []) (Sw12 ∷ Sw34 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ [])
  b5 = at 5 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0004 c4) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0004 c4) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0003 c4) ▸ done

  b6 : Chain (Sw12 ∷ Sw34 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ []) (Sw12 ∷ Sw34 ∷ CCZ013 ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ [])
  b6 = at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0003 c4) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0003 c4) ▸
       at 3 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸ done

  b7 : Chain (Sw12 ∷ Sw34 ∷ CCZ013 ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ []) (CCZ024 ∷ Sw34 ∷ [])
  b7 = at 1 3 (CCZ014 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (CCZ024 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm push TOFF302 sw3 R: 76 steps
lem-comm-push-TOFF302-sw3-R : WsL → ⟪ (Sw34 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ Sw34 ∷ []) ⟫ʷ
lem-comm-push-TOFF302-sw3-R c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (run b9)))))))))
  where
  b0 : Chain (Sw34 ∷ Toff302 ∷ []) (Sw34 ∷ Sw12 ∷ K3 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Toff301 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (K3 ∷ Sw23 ∷ []) (sym (wl0064 c4)) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸ done

  b1 : Chain (Sw34 ∷ Sw12 ∷ K3 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw12 ∷ []) (Sw34 ∷ K3 ∷ Sw12 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw12 ∷ [])
  b1 = at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K3 ∷ Sw23 ∷ []) (sym (wl0064 c4)) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 10 2 [] (wl0003 c4) ▸
       at 1 2 (K3 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K)) ▸ done

  b2 : Chain (Sw34 ∷ K3 ∷ Sw12 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw12 ∷ []) (Sw34 ∷ K3 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K3 ∷ Sw12 ∷ ι ∷ Sw12 ∷ [])
  b2 = at 2 2 (CS23 ∷ Sw12 ∷ []) (sym (wl0047 c4)) ▸
       at 5 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 3 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS23⁻ ∷ Sw12 ∷ []) (sym (wl0029 c4)) ▸
       at 7 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 5 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 7 2 (K3 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K)) ▸ done

  b3 : Chain (Sw34 ∷ K3 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K3 ∷ Sw12 ∷ ι ∷ Sw12 ∷ []) (K4 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ Sw34 ∷ CX02 ∷ CS03 ∷ K3 ∷ ι ∷ [])
  b3 = at 8 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 9 2 [] (wl0006 c4) ▸
       at 0 2 (K4 ∷ Sw34 ∷ []) (sym (wl0065 c4)) ▸
       at 3 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 3 (CS24 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CX02 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap))) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (K4 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ Sw34 ∷ CX02 ∷ CS03 ∷ K3 ∷ ι ∷ []) (Sw12 ∷ K4 ∷ CS14 ∷ Sw12 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K4 ∷ ι ∷ Sw34 ∷ [])
  b4 = at 4 2 (CX02 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap))) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 5 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K4 ∷ Sw34 ∷ []) (sym (wl0065 c4)) ▸
       at 7 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 1 2 (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑)) ▸
       at 2 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 c4)) ▸ done

  b5 : Chain (Sw12 ∷ K4 ∷ CS14 ∷ Sw12 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K4 ∷ ι ∷ Sw34 ∷ []) (Sw12 ∷ K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw34 ∷ [])
  b5 = at 4 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0006 c4) ▸
       at 4 2 (CS14⁻ ∷ Sw12 ∷ []) (sym (wl0014 c4)) ▸
       at 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0006 c4) ▸
       at 6 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R c4) ▸
       at 7 2 (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑)) ▸
       at 8 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸ done

  b6 : Chain (Sw12 ∷ K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw34 ∷ []) (Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw34 ∷ CS04 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw34 ∷ [])
  b6 = at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 2 (K3 ∷ Sw34 ∷ []) (sym (wl0066 c4)) ▸
       at 4 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0004 c4) ▸
       at 4 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 6 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0004 c4) ▸
       at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸ done

  b7 : Chain (Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw34 ∷ CS04 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw34 ∷ []) (Sw12 ∷ Sw34 ∷ Sw23 ∷ K2 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ [])
  b7 = at 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0004 c4) ▸
       at 8 2 (K3 ∷ Sw34 ∷ []) (sym (wl0066 c4)) ▸
       at 9 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 3 2 (K2 ∷ Sw23 ∷ []) (sym (wl0067 c4)) ▸
       at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0003 c4) ▸ done

  b8 : Chain (Sw12 ∷ Sw34 ∷ Sw23 ∷ K2 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ []) (Sw12 ∷ Sw34 ∷ Sw23 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ [])
  b8 = at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0003 c4) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0003 c4) ▸
       at 9 2 (K2 ∷ Sw23 ∷ []) (sym (wl0067 c4)) ▸
       at 10 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸ done

  b9 : Chain (Sw12 ∷ Sw34 ∷ Sw23 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ []) (Toff402 ∷ Sw34 ∷ [])
  b9 = at 3 8 (Toff201 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff301 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff401 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff402 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm push BOX(0;31) sw3 R: 4 steps
lem-comm-push-BOX⟨0·31⟩-sw3-R : WsL → ⟪ (Sw34 ∷ Bx0-31 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-41 ∷ Sw34 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·31⟩-sw3-R c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx0-31 ∷ []) (Bx0-41 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ13 ∷ []) (refl) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 0 3 (CZ14 ∷ []) (by-assoc Eq.refl) ▸
       at 0 1 (Bx0-41 ∷ []) (refl) ▸ done


-- comm push BOX(3;021) sw3 R: 8 steps
lem-comm-push-BOX⟨3·021⟩-sw3-R : WsL → ⟪ (Sw34 ∷ Bx3-021 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-021 ∷ Sw34 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨3·021⟩-sw3-R c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx3-021 ∷ []) (Bx4-021 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Toff302 ∷ CCZ023 ∷ Bx0-31 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw34 ∷ []) (lem-comm-push-CCZ023-sw3-R c4) ▸
       at 1 2 (Toff402 ∷ Sw34 ∷ []) (lem-comm-push-TOFF302-sw3-R c4) ▸
       at 2 2 (Bx0-41 ∷ Sw34 ∷ []) (lem-comm-push-BOX⟨0·31⟩-sw3-R c4) ▸
       at 3 2 (Toff402 ∷ Sw34 ∷ []) (lem-comm-push-TOFF302-sw3-R c4) ▸
       at 4 2 (CCZ024 ∷ Sw34 ∷ []) (lem-comm-push-CCZ023-sw3-R c4) ▸
       at 5 2 (Bx0-41 ∷ Sw34 ∷ []) (lem-comm-push-BOX⟨0·31⟩-sw3-R c4) ▸
       at 0 6 (Bx4-021 ∷ []) (refl) ▸ done


-- comm push BOX(0;3421) sw3 R: 8 steps
lem-comm-push-BOX⟨0·3421⟩-sw3-R : WsL → ⟪ (Sw34 ∷ Bx0-3421 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4321 ∷ Sw34 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·3421⟩-sw3-R c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx0-3421 ∷ []) (Bx0-4321 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff034 ∷ Bx3-021 ∷ Toff034 ∷ CCZ034 ∷ Bx3-021 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw34 ∷ []) (lem-comm-push-CCZ034-sw3-R c4) ▸
       at 1 2 (Toff034 ∷ Sw34 ∷ []) (lem-comm-push-TOFF034-sw3-R c4) ▸
       at 2 2 (Bx4-021 ∷ Sw34 ∷ []) (lem-comm-push-BOX⟨3·021⟩-sw3-R c4) ▸
       at 3 2 (Toff034 ∷ Sw34 ∷ []) (lem-comm-push-TOFF034-sw3-R c4) ▸
       at 4 2 (CCZ034 ∷ Sw34 ∷ []) (lem-comm-push-CCZ034-sw3-R c4) ▸
       at 5 2 (Bx4-021 ∷ Sw34 ∷ []) (lem-comm-push-BOX⟨3·021⟩-sw3-R c4) ▸
       at 0 6 (Bx0-4321 ∷ []) (refl) ▸ done


-- comm push SBOX(0;3;1;2) sw3 R: 4 steps
lem-comm-push-SBOX⟨0·3·1·2⟩-sw3-R : WsL → ⟪ (Sw34 ∷ Sb0-3-1-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-4-1-2 ∷ Sw34 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨0·3·1·2⟩-sw3-R c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb0-3-1-2 ∷ []) (Sb0-4-1-2 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS13 ∷ []) (refl) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 0 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 0 1 (Sb0-4-1-2 ∷ []) (refl) ▸ done


-- comm push SBOXd(0;3;1;2) sw3 R: 4 steps
lem-comm-push-SBOXd⟨0·3·1·2⟩-sw3-R : WsL → ⟪ (Sw34 ∷ Sb⁻0-3-1-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-4-1-2 ∷ Sw34 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨0·3·1·2⟩-sw3-R c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻0-3-1-2 ∷ []) (Sb⁻0-4-1-2 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS13⁻ ∷ []) (refl) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 0 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 0 1 (Sb⁻0-4-1-2 ∷ []) (refl) ▸ done


-- comm push SBOX(0;3;42;1) sw3 R: 9 steps
lem-comm-push-SBOX⟨0·3·42·1⟩-sw3-R : WsL → ⟪ (Sw34 ∷ Sb0-3-42-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-4-32-1 ∷ Sw34 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨0·3·42·1⟩-sw3-R c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw34 ∷ Sb0-3-42-1 ∷ []) (Bx0-4321 ∷ Toff123 ∷ Sb0-4-1-2 ∷ Toff123 ∷ Sb⁻0-4-1-2 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx0-3421 ∷ Toff124 ∷ Sb0-3-1-2 ∷ Toff124 ∷ Sb⁻0-3-1-2 ∷ []) (refl) ▸
       at 0 2 (Bx0-4321 ∷ Sw34 ∷ []) (lem-comm-push-BOX⟨0·3421⟩-sw3-R c4) ▸
       at 2 1 (Sw34 ∷ Toff123 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0004 c4) ▸
       at 2 2 (Sb0-4-1-2 ∷ Sw34 ∷ []) (lem-comm-push-SBOX⟨0·3·1·2⟩-sw3-R c4) ▸
       at 4 1 (Sw34 ∷ Toff123 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0004 c4) ▸
       at 4 2 (Sb⁻0-4-1-2 ∷ Sw34 ∷ []) (lem-comm-push-SBOXd⟨0·3·1·2⟩-sw3-R c4) ▸ done

  b1 : Chain (Bx0-4321 ∷ Toff123 ∷ Sb0-4-1-2 ∷ Toff123 ∷ Sb⁻0-4-1-2 ∷ Sw34 ∷ []) (Sb0-4-32-1 ∷ Sw34 ∷ [])
  b1 = at 0 5 (Sb0-4-32-1 ∷ []) (refl) ▸ done


-- comm push CCZ034 sw1 R: 83 steps
lem-comm-push-CCZ034-sw1-R : WsL → ⟪ (Sw12 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-CCZ034-sw1-R c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (run b10))))))))))
  where
  b0 : Chain (Sw12 ∷ CCZ034 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CCZ024 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw12 ∷ CCZ014 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ CCZ013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸ done

  b1 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ CS14 ∷ Sw34 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b1 = at 8 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (wl0003 c4) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ CS14 ∷ Sw34 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Sw12 ∷ Sw23 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw12 ∷ Sw23 ∷ [])
  b2 = at 4 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 5 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 9 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 7 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0004 c4) ▸
       at 2 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0005 c4)) ▸ done

  b3 : Chain (Sw12 ∷ Sw23 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw12 ∷ Sw23 ∷ []) (Sw12 ∷ CS34 ∷ Sw23 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ Sw23 ∷ [])
  b3 = at 5 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 3 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS24⁻ ∷ Sw12 ∷ []) (sym (wl0007 c4)) ▸
       at 7 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 5 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R c4) ▸
       at 7 2 [] (wl0006 c4) ▸
       at 1 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0008 c4)) ▸ done

  b4 : Chain (Sw12 ∷ CS34 ∷ Sw23 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ Sw23 ∷ []) (CS34 ∷ Sw12 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ [])
  b4 = at 4 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 2 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0009 c4)) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS04 ∷ Sw23 ∷ []) (lem-comm-push-CS04-sw2-R c4) ▸
       at 6 2 [] (wl0003 c4) ▸
       at 0 2 (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸ done

  b5 : Chain (CS34 ∷ Sw12 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ []) (Sw23 ∷ CS24 ∷ CX02 ∷ Sw23 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Sw12 ∷ [])
  b5 = at 1 2 (CX03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸
       at 2 2 (CS34⁻ ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS • CS • CS)) ▸
       at 3 2 (CX03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸
       at 4 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R c4) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0011 c4)) ▸
       at 3 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0003 c4) ▸ done

  b6 : Chain (Sw23 ∷ CS24 ∷ CX02 ∷ Sw23 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ CS14 ∷ CX01 ∷ Sw12 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ Sw23 ∷ Sw12 ∷ [])
  b6 = at 3 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0012 c4)) ▸
       at 5 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0003 c4) ▸
       at 5 2 (CS04 ∷ Sw23 ∷ []) (lem-comm-push-CS04-sw2-R c4) ▸
       at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 2 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 c4)) ▸
       at 4 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0006 c4) ▸ done

  b7 : Chain (Sw23 ∷ Sw12 ∷ CS14 ∷ CX01 ∷ Sw12 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ Sw23 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ Sw34 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ [])
  b7 = at 4 2 (CS14⁻ ∷ Sw12 ∷ []) (sym (wl0014 c4)) ▸
       at 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0006 c4) ▸
       at 6 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R c4) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 4 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0004 c4) ▸
       at 4 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸ done

  b8 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ Sw34 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ [])
  b8 = at 6 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0004 c4) ▸
       at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0004 c4) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0003 c4) ▸ done

  b9 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ CCZ013 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ [])
  b9 = at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0003 c4) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0003 c4) ▸
       at 4 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸ done

  b10 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ CCZ013 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (CCZ034 ∷ Sw12 ∷ [])
  b10 = at 2 3 (CCZ014 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (CCZ024 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (CCZ034 ∷ []) (by-assoc Eq.refl) ▸ done


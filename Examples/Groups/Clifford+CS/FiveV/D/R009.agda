{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.FiveV.D.R009 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.FiveV.WinSig using (WsL ; wl0001 ; wl0003 ; wl0004 ; wl0005 ; wl0006 ; wl0007 ; wl0008 ; wl0009 ; wl0011 ; wl0012 ; wl0013 ; wl0014 ; wl0018 ; wl0019 ; wl0020 ; wl0021 ; wl0022 ; wl0028 ; wl0029 ; wl0033 ; wl0034 ; wl0035 ; wl0036 ; wl0037 ; wl0039 ; wl0040 ; wl0043 ; wl0044 ; wl0046 ; wl0047 ; wl0049 ; wl0057 ; wl0058 ; wl0059 ; wl0060 ; wl0063 ; wl0064 ; wl0065 ; wl0066 ; wl0067 ; wl0069 ; wl0075 ; wl0079 ; wl0083 ; wl0084 ; wl0085 ; wl0086 ; wl0089 ; wl0096 ; wl0105 ; wl0106 ; wl0118 ; wl0119 ; wl0120 ; wl0122 ; wl0126 ; wl0128 ; wl0129 ; wl0143 ; wl0144 ; wl0145 ; wl0146 ; wl0147 ; wl0148 ; wl0149 ; wl0150 ; wl0151 ; wl0152 ; wl0153 ; wl0154)
open import Examples.Groups.Clifford+CS.FiveV.Chain
open import Examples.Groups.Clifford+CS.FiveV.D.R001 using (lem-comm-push-CS04-sw1-R ; lem-comm-push-CS04-sw2-R)
open import Examples.Groups.Clifford+CS.FiveV.D.R006 using (lem-comm-push-CCZ014-sw0-R ; lem-comm-push-CCZ014-sw2-R ; lem-comm-push-CS14-sw0-R ; lem-comm-push-TOFF014-sw2-R)
open import Examples.Groups.Clifford+CS.FiveV.D.R007 using (lem-comm-push-CCZ034-sw3-R ; lem-comm-push-CX04-sw1-R ; lem-comm-push-CX04-sw2-R)
open import Examples.Groups.Clifford+CS.FiveV.D.R008 using (lem-comm-push-BOX⟨4·1320⟩-sw2-R ; lem-comm-push-CCZ024-sw0-R ; lem-comm-push-CCZ124-sw0-R ; lem-comm-push-TOFF024-sw0-R ; lem-comm-push-TOFF401-sw0-R)
-- comm push SBOX(4;1;32;0) sw2 R: 7 steps
lem-comm-push-SBOX⟨4·1·32·0⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Sb4-1-32-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-1-23-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨4·1·32·0⟩-sw2-R c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb4-1-32-0 ∷ []) (Sb4-1-23-0 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx4-1320 ∷ Toff023 ∷ Sb4-1-0-2 ∷ Toff023 ∷ Sb⁻4-1-0-2 ∷ []) (refl) ▸
       at 0 2 (Bx4-1230 ∷ Sw23 ∷ []) (lem-comm-push-BOX⟨4·1320⟩-sw2-R c4) ▸
       at 1 2 (Toff023 ∷ Sw23 ∷ []) (wl0143 c4) ▸
       at 2 2 (Sb4-1-0-2 ∷ Sw23 ∷ []) (sym (c₂ (CS) (Swap))) ▸
       at 3 2 (Toff023 ∷ Sw23 ∷ []) (wl0143 c4) ▸
       at 4 2 (Sb⁻4-1-0-2 ∷ Sw23 ∷ []) (sym (c₂ (CS • CS • CS) (Swap))) ▸
       at 0 5 (Sb4-1-23-0 ∷ []) (refl) ▸ done


-- comm push BOX(4;10) sw1 R: 4 steps
lem-comm-push-BOX⟨4·10⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Bx4-10 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-20 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨4·10⟩-sw1-R c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-10 ∷ []) (Bx4-20 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ01 ∷ []) (refl) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 0 3 (CZ02 ∷ []) (by-assoc Eq.refl) ▸
       at 0 1 (Bx4-20 ∷ []) (refl) ▸ done


-- comm push BOX(1;430) sw1 R: 8 steps
lem-comm-push-BOX⟨1·430⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Bx1-430 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-430 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨1·430⟩-sw1-R c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-430 ∷ []) (Bx2-430 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff134 ∷ Bx4-10 ∷ Toff134 ∷ CCZ134 ∷ Bx4-10 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0044 c4)) ▸
       at 1 2 (Toff234 ∷ Sw12 ∷ []) (wl0083 c4) ▸
       at 2 2 (Bx4-20 ∷ Sw12 ∷ []) (lem-comm-push-BOX⟨4·10⟩-sw1-R c4) ▸
       at 3 2 (Toff234 ∷ Sw12 ∷ []) (wl0083 c4) ▸
       at 4 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0044 c4)) ▸
       at 5 2 (Bx4-20 ∷ Sw12 ∷ []) (lem-comm-push-BOX⟨4·10⟩-sw1-R c4) ▸
       at 0 6 (Bx2-430 ∷ []) (refl) ▸ done


-- comm push BOX(4;1230) sw1 R: 8 steps
lem-comm-push-BOX⟨4·1230⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Bx4-1230 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2130 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨4·1230⟩-sw1-R c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-1230 ∷ []) (Bx4-2130 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff412 ∷ Bx1-430 ∷ Toff412 ∷ CCZ124 ∷ Bx1-430 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0122 c4)) ▸
       at 1 2 (Toff412 ∷ Sw12 ∷ []) (wl0144 c4) ▸
       at 2 2 (Bx2-430 ∷ Sw12 ∷ []) (lem-comm-push-BOX⟨1·430⟩-sw1-R c4) ▸
       at 3 2 (Toff412 ∷ Sw12 ∷ []) (wl0144 c4) ▸
       at 4 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0122 c4)) ▸
       at 5 2 (Bx2-430 ∷ Sw12 ∷ []) (lem-comm-push-BOX⟨1·430⟩-sw1-R c4) ▸
       at 0 6 (Bx4-2130 ∷ []) (refl) ▸ done


-- comm push SBOX(4;1;0;3) sw1 R: 4 steps
lem-comm-push-SBOX⟨4·1·0·3⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Sb4-1-0-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-2-0-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨4·1·0·3⟩-sw1-R c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb4-1-0-3 ∷ []) (Sb4-2-0-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS01 ∷ []) (refl) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 0 3 (CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 0 1 (Sb4-2-0-3 ∷ []) (refl) ▸ done


-- comm push SBOXd(4;1;0;3) sw1 R: 4 steps
lem-comm-push-SBOXd⟨4·1·0·3⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Sb⁻4-1-0-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-2-0-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨4·1·0·3⟩-sw1-R c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻4-1-0-3 ∷ []) (Sb⁻4-2-0-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS01⁻ ∷ []) (refl) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 0 3 (CS02⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 0 1 (Sb⁻4-2-0-3 ∷ []) (refl) ▸ done


-- comm push SBOX(4;1;23;0) sw1 R: 9 steps
lem-comm-push-SBOX⟨4·1·23·0⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Sb4-1-23-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-2-13-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨4·1·23·0⟩-sw1-R c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw12 ∷ Sb4-1-23-0 ∷ []) (Bx4-2130 ∷ Toff013 ∷ Sb4-2-0-3 ∷ Toff013 ∷ Sb⁻4-2-0-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx4-1230 ∷ Toff023 ∷ Sb4-1-0-3 ∷ Toff023 ∷ Sb⁻4-1-0-3 ∷ []) (refl) ▸
       at 0 2 (Bx4-2130 ∷ Sw12 ∷ []) (lem-comm-push-BOX⟨4·1230⟩-sw1-R c4) ▸
       at 2 1 (Sw12 ∷ Toff013 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0006 c4) ▸
       at 2 2 (Sb4-2-0-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨4·1·0·3⟩-sw1-R c4) ▸
       at 4 1 (Sw12 ∷ Toff013 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0006 c4) ▸
       at 4 2 (Sb⁻4-2-0-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOXd⟨4·1·0·3⟩-sw1-R c4) ▸ done

  b1 : Chain (Bx4-2130 ∷ Toff013 ∷ Sb4-2-0-3 ∷ Toff013 ∷ Sb⁻4-2-0-3 ∷ Sw12 ∷ []) (Sb4-2-13-0 ∷ Sw12 ∷ [])
  b1 = at 0 5 (Sb4-2-13-0 ∷ []) (refl) ▸ done


-- comm push TOFF412 sw0 R: 62 steps
lem-comm-push-TOFF412-sw0-R : WsL → ⟪ (Sw01 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-TOFF412-sw0-R c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (Sw01 ∷ Toff412 ∷ []) (Sw01 ∷ K4 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Sw34 ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Toff312 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (K4 ∷ Sw34 ∷ []) (sym (wl0065 c4)) ▸
       at 4 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 3 (CS24 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 4 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw01 ∷ K4 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Sw34 ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ Sw34 ∷ []) (K4 ∷ CS24 ∷ Sw01 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K4 ∷ ι1 ∷ [])
  b1 = at 5 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 6 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K4 ∷ Sw34 ∷ []) (sym (wl0065 c4)) ▸
       at 8 2 (ι1 ∷ Sw34 ∷ []) (sym (c₂ (iI ↑) (Swap ↑))) ▸
       at 9 2 [] (wl0004 c4) ▸
       at 0 2 (K4 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ ↑)) ▸
       at 1 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸ done

  b2 : Chain (K4 ∷ CS24 ∷ Sw01 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K4 ∷ ι1 ∷ []) (Sw12 ∷ K4 ∷ Sw12 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K4 ∷ ι1 ∷ Sw01 ∷ [])
  b2 = at 2 2 (CX02 ∷ Sw01 ∷ []) (sym (wl0039 c4)) ▸
       at 3 2 (CS24⁻ ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • (CS • CS • CS) • Swap ↑)) ▸
       at 4 2 (CX02 ∷ Sw01 ∷ []) (sym (wl0039 c4)) ▸
       at 5 2 (CS04 ∷ Sw01 ∷ []) (lem-comm-push-CS14-sw0-R c4) ▸
       at 6 2 (K4 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ ↑)) ▸
       at 7 2 (ι1 ∷ Sw01 ∷ []) (wl0118 c4) ▸
       at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 1 2 (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑)) ▸ done

  b3 : Chain (Sw12 ∷ K4 ∷ Sw12 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K4 ∷ ι1 ∷ Sw01 ∷ []) (Sw12 ∷ K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K4 ∷ Sw12 ∷ ι1 ∷ Sw01 ∷ [])
  b3 = at 2 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 c4)) ▸
       at 4 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0006 c4) ▸
       at 4 2 (CS14⁻ ∷ Sw12 ∷ []) (sym (wl0014 c4)) ▸
       at 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0006 c4) ▸
       at 6 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R c4) ▸
       at 7 2 (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑)) ▸ done

  b4 : Chain (Sw12 ∷ K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K4 ∷ Sw12 ∷ ι1 ∷ Sw01 ∷ []) (Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw34 ∷ CX01 ∷ CS04 ∷ K4 ∷ ι1 ∷ Sw12 ∷ Sw01 ∷ [])
  b4 = at 8 2 (ι1 ∷ Sw12 ∷ []) (wl0119 c4) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 2 (K3 ∷ Sw34 ∷ []) (sym (wl0066 c4)) ▸
       at 4 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0004 c4) ▸
       at 4 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 6 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0004 c4) ▸ done

  b5 : Chain (Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw34 ∷ CX01 ∷ CS04 ∷ K4 ∷ ι1 ∷ Sw12 ∷ Sw01 ∷ []) (Sw12 ∷ Sw34 ∷ Sw23 ∷ K2 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι1 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ [])
  b5 = at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0004 c4) ▸
       at 8 2 (K3 ∷ Sw34 ∷ []) (sym (wl0066 c4)) ▸
       at 9 2 (ι1 ∷ Sw34 ∷ []) (sym (c₂ (iI ↑) (Swap ↑))) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 3 2 (K2 ∷ Sw23 ∷ []) (sym (wl0067 c4)) ▸
       at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b6 : Chain (Sw12 ∷ Sw34 ∷ Sw23 ∷ K2 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι1 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ []) (Sw12 ∷ Sw34 ∷ Sw23 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ Sw23 ∷ ι1 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ [])
  b6 = at 4 2 [] (wl0003 c4) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0003 c4) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0003 c4) ▸
       at 9 2 (K2 ∷ Sw23 ∷ []) (sym (wl0067 c4)) ▸ done

  b7 : Chain (Sw12 ∷ Sw34 ∷ Sw23 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ Sw23 ∷ ι1 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ []) (Toff402 ∷ Sw01 ∷ [])
  b7 = at 10 2 (ι1 ∷ Sw23 ∷ []) (sym (c₂ (iI ↑) (Swap))) ▸
       at 3 8 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (sym (wl0120 c4)) ▸
       at 3 8 (Toff201 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff301 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff401 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff402 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm push BOX(4;20) sw0 R: 3 steps
lem-comm-push-BOX⟨4·20⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Bx4-20 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-21 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨4·20⟩-sw0-R c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-20 ∷ []) (Bx4-21 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ02 ∷ []) (refl) ▸
       at 0 2 (CZ12 ∷ Sw01 ∷ []) (sym (wl0145 c4)) ▸
       at 0 1 (Bx4-21 ∷ []) (refl) ▸ done


-- comm push BOX(2;430) sw0 R: 8 steps
lem-comm-push-BOX⟨2·430⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Bx2-430 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-431 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨2·430⟩-sw0-R c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-430 ∷ []) (Bx2-431 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff234 ∷ Bx4-20 ∷ Toff234 ∷ CCZ234 ∷ Bx4-20 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 1 2 (Toff234 ∷ Sw01 ∷ []) (c₂ (Swap) (Toff)) ▸
       at 2 2 (Bx4-21 ∷ Sw01 ∷ []) (lem-comm-push-BOX⟨4·20⟩-sw0-R c4) ▸
       at 3 2 (Toff234 ∷ Sw01 ∷ []) (c₂ (Swap) (Toff)) ▸
       at 4 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 5 2 (Bx4-21 ∷ Sw01 ∷ []) (lem-comm-push-BOX⟨4·20⟩-sw0-R c4) ▸
       at 0 6 (Bx2-431 ∷ []) (refl) ▸ done


-- comm push BOX(4;2130) sw0 R: 8 steps
lem-comm-push-BOX⟨4·2130⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Bx4-2130 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2031 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨4·2130⟩-sw0-R c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-2130 ∷ []) (Bx4-2031 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff412 ∷ Bx2-430 ∷ Toff412 ∷ CCZ124 ∷ Bx2-430 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw01 ∷ []) (lem-comm-push-CCZ124-sw0-R c4) ▸
       at 1 2 (Toff402 ∷ Sw01 ∷ []) (lem-comm-push-TOFF412-sw0-R c4) ▸
       at 2 2 (Bx2-431 ∷ Sw01 ∷ []) (lem-comm-push-BOX⟨2·430⟩-sw0-R c4) ▸
       at 3 2 (Toff402 ∷ Sw01 ∷ []) (lem-comm-push-TOFF412-sw0-R c4) ▸
       at 4 2 (CCZ024 ∷ Sw01 ∷ []) (lem-comm-push-CCZ124-sw0-R c4) ▸
       at 5 2 (Bx2-431 ∷ Sw01 ∷ []) (lem-comm-push-BOX⟨2·430⟩-sw0-R c4) ▸
       at 0 6 (Bx4-2031 ∷ []) (refl) ▸ done


-- comm push SBOX(4;2;0;3) sw0 R: 3 steps
lem-comm-push-SBOX⟨4·2·0·3⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Sb4-2-0-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-2-1-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨4·2·0·3⟩-sw0-R c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb4-2-0-3 ∷ []) (Sb4-2-1-3 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS02 ∷ []) (refl) ▸
       at 0 2 (CS12 ∷ Sw01 ∷ []) (sym (wl0146 c4)) ▸
       at 0 1 (Sb4-2-1-3 ∷ []) (refl) ▸ done


-- comm push SBOXd(4;2;0;3) sw0 R: 3 steps
lem-comm-push-SBOXd⟨4·2·0·3⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Sb⁻4-2-0-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-2-1-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨4·2·0·3⟩-sw0-R c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻4-2-0-3 ∷ []) (Sb⁻4-2-1-3 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS02⁻ ∷ []) (refl) ▸
       at 0 2 (CS12⁻ ∷ Sw01 ∷ []) (sym (wl0147 c4)) ▸
       at 0 1 (Sb⁻4-2-1-3 ∷ []) (refl) ▸ done


-- comm push SBOX(4;2;13;0) sw0 R: 7 steps
lem-comm-push-SBOX⟨4·2·13·0⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Sb4-2-13-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-2-03-1 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨4·2·13·0⟩-sw0-R c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb4-2-13-0 ∷ []) (Sb4-2-03-1 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx4-2130 ∷ Toff013 ∷ Sb4-2-0-3 ∷ Toff013 ∷ Sb⁻4-2-0-3 ∷ []) (refl) ▸
       at 0 2 (Bx4-2031 ∷ Sw01 ∷ []) (lem-comm-push-BOX⟨4·2130⟩-sw0-R c4) ▸
       at 1 2 (Toff103 ∷ Sw01 ∷ []) (wl0148 c4) ▸
       at 2 2 (Sb4-2-1-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨4·2·0·3⟩-sw0-R c4) ▸
       at 3 2 (Toff103 ∷ Sw01 ∷ []) (wl0148 c4) ▸
       at 4 2 (Sb⁻4-2-1-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOXd⟨4·2·0·3⟩-sw0-R c4) ▸
       at 0 5 (Sb4-2-03-1 ∷ []) (refl) ▸ done


-- comm CSd13 TOFF402: 11 steps
lem-comm-CSd13-TOFF402 : WsL → ⟪ (CS13⁻ ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-comm-CSd13-TOFF402 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS13⁻ ∷ Toff402 ∷ []) (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ CS23⁻ ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ CS23⁻ ∷ []) (wl0028 c4) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw23 ∷ CS34⁻ ∷ []) (wl0012 c4) ▸
       at 3 2 (Toff201 ∷ CS34⁻ ∷ []) (sym (c₃ (Toffᵗ) (CS • CS • CS))) ▸
       at 4 2 (Sw23 ∷ CS24⁻ ∷ []) (wl0009 c4) ▸
       at 5 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ CS23⁻ ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ []) (Toff402 ∷ CS13⁻ ∷ [])
  b1 = at 7 2 [] (wl0004 c4) ▸
       at 6 2 (Sw12 ∷ CS13⁻ ∷ []) (wl0029 c4) ▸
       at 0 7 (Toff402 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CS13 TOFF402: 11 steps
lem-comm-CS13-TOFF402 : WsL → ⟪ (CS13 ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ CS13 ∷ []) ⟫ʷ
lem-comm-CS13-TOFF402 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS13 ∷ Toff402 ∷ []) (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ CS23 ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ CS23 ∷ []) (wl0046 c4) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 3 (CS24 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw23 ∷ CS34 ∷ []) (wl0011 c4) ▸
       at 3 2 (Toff201 ∷ CS34 ∷ []) (sym (c₃ (Toffᵗ) (CS))) ▸
       at 4 2 (Sw23 ∷ CS24 ∷ []) (wl0008 c4) ▸
       at 5 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ CS23 ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ []) (Toff402 ∷ CS13 ∷ [])
  b1 = at 7 2 [] (wl0004 c4) ▸
       at 6 2 (Sw12 ∷ CS13 ∷ []) (wl0047 c4) ▸
       at 0 7 (Toff402 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm SWAP03 BOX(4;21): 3 steps
lem-comm-SWAP03-BOX⟨4·21⟩ : WsL → ⟪ (Sw03 ∷ Bx4-21 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-21 ∷ Sw03 ∷ []) ⟫ʷ
lem-comm-SWAP03-BOX⟨4·21⟩ c4 = run b0
  where
  b0 : Chain (Sw03 ∷ Bx4-21 ∷ []) (Bx4-21 ∷ Sw03 ∷ [])
  b0 = at 1 1 (CZ12 ∷ []) (refl) ▸
       at 0 2 (CZ12 ∷ Sw03 ∷ []) (sym (wl0086 c4)) ▸
       at 0 1 (Bx4-21 ∷ []) (refl) ▸ done


-- comm TOFF402 CSd13: 11 steps
lem-comm-TOFF402-CSd13 : WsL → ⟪ (Toff402 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ Toff402 ∷ []) ⟫ʷ
lem-comm-TOFF402-CSd13 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff402 ∷ CS13⁻ ∷ []) (Sw12 ∷ Sw34 ∷ Sw34 ∷ CS23⁻ ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ [])
  b0 = at 0 1 (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS23⁻ ∷ Sw12 ∷ []) (sym (wl0029 c4)) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 5 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0009 c4)) ▸
       at 3 2 (CS34⁻ ∷ Toff201 ∷ []) (c₃ (Toffᵗ) (CS • CS • CS)) ▸
       at 2 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0012 c4)) ▸
       at 2 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ Sw34 ∷ Sw34 ∷ CS23⁻ ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) (CS13⁻ ∷ Toff402 ∷ [])
  b1 = at 1 2 [] (wl0004 c4) ▸
       at 0 2 (CS13⁻ ∷ Sw12 ∷ []) (sym (wl0028 c4)) ▸
       at 1 7 (Toff402 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CSd02 TOFF413: 23 steps
lem-comm-CSd02-TOFF413 : WsL → ⟪ (CS02⁻ ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-comm-CSd02-TOFF413 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS02⁻ ∷ Toff413 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Toff412 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw34 ∷ Toff312 ∷ Sw34 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 3 (CS04⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 8 3 (Toff412 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Toff412 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Toff312 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b1 = at 9 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 7 3 (Toff413 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Toff423 ∷ Sw12 ∷ []) (wl0084 c4) ▸
       at 5 2 (Toff423 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (Toffᵗ)) ▸
       at 4 2 (Toff413 ∷ Sw12 ∷ []) (wl0085 c4) ▸
       at 4 1 (Sw23 ∷ Toff412 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0003 c4) ▸
       at 3 1 (Sw34 ∷ Toff312 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Toff312 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (Toff413 ∷ CS02⁻ ∷ [])
  b2 = at 2 2 [] (wl0004 c4) ▸
       at 3 7 (CS04⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ CS03⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0004 c4) ▸
       at 4 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0003 c4) ▸
       at 0 5 (Toff413 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CK02 TOFF413: 23 steps
lem-comm-CK02-TOFF413 : WsL → ⟪ (CK02 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CK02 ∷ []) ⟫ʷ
lem-comm-CK02-TOFF413 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CK02 ∷ Toff413 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ Toff412 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw34 ∷ Toff312 ∷ Sw34 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (CK03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 3 (CK04 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 8 3 (Toff412 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ Toff412 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Toff312 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b1 = at 9 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 7 3 (Toff413 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Toff423 ∷ Sw12 ∷ []) (wl0084 c4) ▸
       at 5 2 (Toff423 ∷ CK01 ∷ []) (c₂ (CK₀₁) (Toffᵗ)) ▸
       at 4 2 (Toff413 ∷ Sw12 ∷ []) (wl0085 c4) ▸
       at 4 1 (Sw23 ∷ Toff412 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0003 c4) ▸
       at 3 1 (Sw34 ∷ Toff312 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Toff312 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (Toff413 ∷ CK02 ∷ [])
  b2 = at 2 2 [] (wl0004 c4) ▸
       at 3 7 (CK04 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ CK03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0004 c4) ▸
       at 4 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0003 c4) ▸
       at 0 5 (Toff413 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm push BOX(2;03) sw2 R: 4 steps
lem-comm-push-BOX⟨2·03⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Bx2-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-02 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨2·03⟩-sw2-R c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-03 ∷ []) (Bx3-02 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ03 ∷ []) (refl) ▸
       at 1 1 (Sw23 ∷ CZ02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0003 c4) ▸
       at 0 1 (Bx3-02 ∷ []) (refl) ▸ done


-- comm push BOX(0;213) sw2 R: 12 steps
lem-comm-push-BOX⟨0·213⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Bx0-213 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-312 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·213⟩-sw2-R c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw23 ∷ Bx0-213 ∷ []) (CCZ013 ∷ Toff013 ∷ Bx3-02 ∷ Toff013 ∷ Sw23 ∷ CCZ012 ∷ Bx2-03 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) (refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 0 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Bx3-02 ∷ Sw23 ∷ []) (lem-comm-push-BOX⟨2·03⟩-sw2-R c4) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 3 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (CCZ013 ∷ Toff013 ∷ Bx3-02 ∷ Toff013 ∷ Sw23 ∷ CCZ012 ∷ Bx2-03 ∷ []) (Bx0-312 ∷ Sw23 ∷ [])
  b1 = at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Bx3-02 ∷ Sw23 ∷ []) (lem-comm-push-BOX⟨2·03⟩-sw2-R c4) ▸
       at 0 6 (Bx0-312 ∷ []) (refl) ▸ done


-- comm push BOX(2;0413) sw2 R: 12 steps
lem-comm-push-BOX⟨2·0413⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨2·0413⟩-sw2-R c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw23 ∷ Bx2-0413 ∷ []) (CCZ034 ∷ Toff304 ∷ Bx0-312 ∷ Toff304 ∷ Sw23 ∷ CCZ024 ∷ Bx0-213 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ []) (refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 0 3 (CCZ034 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (Toff304 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Bx0-312 ∷ Sw23 ∷ []) (lem-comm-push-BOX⟨0·213⟩-sw2-R c4) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 3 3 (Toff304 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff304 ∷ Bx0-312 ∷ Toff304 ∷ Sw23 ∷ CCZ024 ∷ Bx0-213 ∷ []) (Bx3-0412 ∷ Sw23 ∷ [])
  b1 = at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (CCZ034 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Bx0-312 ∷ Sw23 ∷ []) (lem-comm-push-BOX⟨0·213⟩-sw2-R c4) ▸
       at 0 6 (Bx3-0412 ∷ []) (refl) ▸ done


-- comm push SBOX(2;0;3;1) sw2 R: 4 steps
lem-comm-push-SBOX⟨2·0·3·1⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Sb2-0-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-2-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨2·0·3·1⟩-sw2-R c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb2-0-3-1 ∷ []) (Sb3-0-2-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS03 ∷ []) (refl) ▸
       at 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0003 c4) ▸
       at 0 1 (Sb3-0-2-1 ∷ []) (refl) ▸ done


-- comm push SBOXd(2;0;3;1) sw2 R: 4 steps
lem-comm-push-SBOXd⟨2·0·3·1⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Sb⁻2-0-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-0-2-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨2·0·3·1⟩-sw2-R c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻2-0-3-1 ∷ []) (Sb⁻3-0-2-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS03⁻ ∷ []) (refl) ▸
       at 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0003 c4) ▸
       at 0 1 (Sb⁻3-0-2-1 ∷ []) (refl) ▸ done


-- comm push SBOX(2;0;41;3) sw2 R: 9 steps
lem-comm-push-SBOX⟨2·0·41·3⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-41-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨2·0·41·3⟩-sw2-R c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw23 ∷ Sb2-0-41-3 ∷ []) (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 0 2 (Bx3-0412 ∷ Sw23 ∷ []) (lem-comm-push-BOX⟨2·0413⟩-sw2-R c4) ▸
       at 2 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0003 c4) ▸
       at 2 2 (Sb3-0-2-1 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨2·0·3·1⟩-sw2-R c4) ▸
       at 4 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0003 c4) ▸
       at 4 2 (Sb⁻3-0-2-1 ∷ Sw23 ∷ []) (lem-comm-push-SBOXd⟨2·0·3·1⟩-sw2-R c4) ▸ done

  b1 : Chain (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ Sw23 ∷ []) (Sb3-0-41-2 ∷ Sw23 ∷ [])
  b1 = at 0 5 (Sb3-0-41-2 ∷ []) (refl) ▸ done


-- comm push TOFF304 sw3 R: 114 steps
lem-comm-push-TOFF304-sw3-R : WsL → ⟪ (Sw34 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ Sw34 ∷ []) ⟫ʷ
lem-comm-push-TOFF304-sw3-R c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (run b14))))))))))))))
  where
  b0 : Chain (Sw34 ∷ Toff304 ∷ []) (Sw34 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Toff204 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw12 ∷ Toff104 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ Toff103 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b1 = at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 7 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 11 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸ done

  b2 : Chain (Sw34 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b2 = at 12 2 [] (wl0003 c4) ▸
       at 3 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 4 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 6 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸ done

  b3 : Chain (Sw34 ∷ Sw23 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ K2 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw23 ∷ [])
  b3 = at 10 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 8 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 10 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 11 2 [] (wl0004 c4) ▸
       at 2 2 (K2 ∷ Sw12 ∷ []) (sym (wl0040 c4)) ▸
       at 3 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0005 c4)) ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸ done

  b4 : Chain (Sw34 ∷ Sw23 ∷ K2 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K2 ∷ ι ∷ Sw23 ∷ [])
  b4 = at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS24⁻ ∷ Sw12 ∷ []) (sym (wl0007 c4)) ▸
       at 8 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 6 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R c4) ▸
       at 8 2 (K2 ∷ Sw12 ∷ []) (sym (wl0040 c4)) ▸
       at 9 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 10 2 [] (wl0006 c4) ▸ done

  b5 : Chain (Sw34 ∷ Sw23 ∷ K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K2 ∷ ι ∷ Sw23 ∷ []) (Sw34 ∷ K3 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Sw23 ∷ K2 ∷ ι ∷ Sw23 ∷ [])
  b5 = at 1 2 (K3 ∷ Sw23 ∷ []) (sym (wl0064 c4)) ▸
       at 2 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0008 c4)) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 3 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0009 c4)) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 5 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS04 ∷ Sw23 ∷ []) (lem-comm-push-CS04-sw2-R c4) ▸ done

  b6 : Chain (Sw34 ∷ K3 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Sw23 ∷ K2 ∷ ι ∷ Sw23 ∷ []) (K4 ∷ CS34 ∷ CX04 ∷ CS34⁻ ∷ Sw34 ∷ CX03 ∷ CS04 ∷ K3 ∷ ι ∷ [])
  b6 = at 7 2 (K3 ∷ Sw23 ∷ []) (sym (wl0064 c4)) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 9 2 [] (wl0003 c4) ▸
       at 0 2 (K4 ∷ Sw34 ∷ []) (sym (wl0065 c4)) ▸
       at 1 2 (CS34 ∷ Sw34 ∷ []) (sym (wl0129 c4)) ▸
       at 4 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 3 (CX04 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS34⁻ ∷ Sw34 ∷ []) (sym (wl0128 c4)) ▸ done

  b7 : Chain (K4 ∷ CS34 ∷ CX04 ∷ CS34⁻ ∷ Sw34 ∷ CX03 ∷ CS04 ∷ K3 ∷ ι ∷ []) (Sw23 ∷ K4 ∷ Sw23 ∷ CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ K4 ∷ ι ∷ Sw34 ∷ [])
  b7 = at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 4 3 (CX04 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0004 c4) ▸
       at 6 2 (K4 ∷ Sw34 ∷ []) (sym (wl0065 c4)) ▸
       at 7 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸ done

  b8 : Chain (Sw23 ∷ K4 ∷ Sw23 ∷ CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ K4 ∷ ι ∷ Sw34 ∷ []) (Sw23 ∷ K4 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ K4 ∷ ι ∷ Sw23 ∷ Sw34 ∷ [])
  b8 = at 2 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0011 c4)) ▸
       at 3 2 (CX04 ∷ Sw23 ∷ []) (lem-comm-push-CX04-sw2-R c4) ▸
       at 4 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0012 c4)) ▸
       at 5 2 (CX04 ∷ Sw23 ∷ []) (lem-comm-push-CX04-sw2-R c4) ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0003 c4) ▸
       at 7 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸ done

  b9 : Chain (Sw23 ∷ K4 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ K4 ∷ ι ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw12 ∷ K4 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ Sw12 ∷ K4 ∷ ι ∷ Sw23 ∷ Sw34 ∷ [])
  b9 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 2 2 (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑)) ▸
       at 3 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 c4)) ▸
       at 4 2 (CX04 ∷ Sw12 ∷ []) (lem-comm-push-CX04-sw1-R c4) ▸
       at 5 2 (CS14⁻ ∷ Sw12 ∷ []) (sym (wl0014 c4)) ▸
       at 6 2 (CX04 ∷ Sw12 ∷ []) (lem-comm-push-CX04-sw1-R c4) ▸
       at 8 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0006 c4) ▸ done

  b10 : Chain (Sw23 ∷ Sw12 ∷ K4 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ Sw12 ∷ K4 ∷ ι ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX03 ∷ Sw34 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ [])
  b10 = at 8 2 (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑)) ▸
       at 9 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 2 (K3 ∷ Sw34 ∷ []) (sym (wl0066 c4)) ▸
       at 5 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0004 c4) ▸
       at 6 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0004 c4) ▸ done

  b11 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX03 ∷ Sw34 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Sw23 ∷ K3 ∷ CS13 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ [])
  b11 = at 7 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0004 c4) ▸
       at 8 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0004 c4) ▸
       at 8 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 9 2 (K3 ∷ Sw34 ∷ []) (sym (wl0066 c4)) ▸
       at 10 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸ done

  b12 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Sw23 ∷ K3 ∷ CS13 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K2 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX02 ∷ Sw23 ∷ CS01 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ [])
  b12 = at 4 2 (K2 ∷ Sw23 ∷ []) (sym (wl0067 c4)) ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0003 c4) ▸
       at 7 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0003 c4) ▸
       at 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0003 c4) ▸
       at 9 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b13 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K2 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX02 ∷ Sw23 ∷ CS01 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw12 ∷ Toff401 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ [])
  b13 = at 8 2 [] (wl0003 c4) ▸
       at 9 2 (CS01 ∷ Sw23 ∷ []) (sym (c₂ (CS) (Swap))) ▸
       at 10 2 (K2 ∷ Sw23 ∷ []) (sym (wl0067 c4)) ▸
       at 11 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 4 8 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (sym (wl0149 c4)) ▸
       at 4 8 (Toff201 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (Toff301 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff401 ∷ []) (by-assoc Eq.refl) ▸ done

  b14 : Chain (Sw23 ∷ Sw12 ∷ Toff401 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (Toff403 ∷ Sw34 ∷ [])
  b14 = at 1 3 (Toff402 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff403 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm push BOX(0;312) sw3 R: 12 steps
lem-comm-push-BOX⟨0·312⟩-sw3-R : WsL → ⟪ (Sw34 ∷ Bx0-312 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-412 ∷ Sw34 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·312⟩-sw3-R c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw34 ∷ Bx0-312 ∷ []) (CCZ014 ∷ Toff014 ∷ Bx3-02 ∷ Toff014 ∷ Sw34 ∷ CCZ013 ∷ Bx3-02 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff013 ∷ Bx3-02 ∷ Toff013 ∷ CCZ013 ∷ Bx3-02 ∷ []) (refl) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 0 3 (CCZ014 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 3 (Toff014 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Bx3-02 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑ • CZ • Swap ↑) (Swap))) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (Toff014 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (CCZ014 ∷ Toff014 ∷ Bx3-02 ∷ Toff014 ∷ Sw34 ∷ CCZ013 ∷ Bx3-02 ∷ []) (Bx0-412 ∷ Sw34 ∷ [])
  b1 = at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 4 3 (CCZ014 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Bx3-02 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑ • CZ • Swap ↑) (Swap))) ▸
       at 0 6 (Bx0-412 ∷ []) (refl) ▸ done


-- comm push BOX(3;0412) sw3 R: 8 steps
lem-comm-push-BOX⟨3·0412⟩-sw3-R : WsL → ⟪ (Sw34 ∷ Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0312 ∷ Sw34 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨3·0412⟩-sw3-R c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx3-0412 ∷ []) (Bx4-0312 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff304 ∷ Bx0-312 ∷ Toff304 ∷ CCZ034 ∷ Bx0-312 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw34 ∷ []) (lem-comm-push-CCZ034-sw3-R c4) ▸
       at 1 2 (Toff403 ∷ Sw34 ∷ []) (lem-comm-push-TOFF304-sw3-R c4) ▸
       at 2 2 (Bx0-412 ∷ Sw34 ∷ []) (lem-comm-push-BOX⟨0·312⟩-sw3-R c4) ▸
       at 3 2 (Toff403 ∷ Sw34 ∷ []) (lem-comm-push-TOFF304-sw3-R c4) ▸
       at 4 2 (CCZ034 ∷ Sw34 ∷ []) (lem-comm-push-CCZ034-sw3-R c4) ▸
       at 5 2 (Bx0-412 ∷ Sw34 ∷ []) (lem-comm-push-BOX⟨0·312⟩-sw3-R c4) ▸
       at 0 6 (Bx4-0312 ∷ []) (refl) ▸ done


-- comm push SBOX(3;0;41;2) sw3 R: 9 steps
lem-comm-push-SBOX⟨3·0·41·2⟩-sw3-R : WsL → ⟪ (Sw34 ∷ Sb3-0-41-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-0-31-2 ∷ Sw34 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨3·0·41·2⟩-sw3-R c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw34 ∷ Sb3-0-41-2 ∷ []) (Bx4-0312 ∷ Toff213 ∷ Sb3-0-2-1 ∷ Toff213 ∷ Sb⁻3-0-2-1 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (refl) ▸
       at 0 2 (Bx4-0312 ∷ Sw34 ∷ []) (lem-comm-push-BOX⟨3·0412⟩-sw3-R c4) ▸
       at 2 1 (Sw34 ∷ Toff213 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0004 c4) ▸
       at 2 2 (Sb3-0-2-1 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑ • CS • Swap ↑) (Swap))) ▸
       at 4 1 (Sw34 ∷ Toff213 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0004 c4) ▸
       at 4 2 (Sb⁻3-0-2-1 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (Swap))) ▸ done

  b1 : Chain (Bx4-0312 ∷ Toff213 ∷ Sb3-0-2-1 ∷ Toff213 ∷ Sb⁻3-0-2-1 ∷ Sw34 ∷ []) (Sb4-0-31-2 ∷ Sw34 ∷ [])
  b1 = at 0 5 (Sb4-0-31-2 ∷ []) (refl) ▸ done


-- comm push BOX(4;02) sw2 R: 4 steps
lem-comm-push-BOX⟨4·02⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Bx4-02 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-03 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨4·02⟩-sw2-R c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-02 ∷ []) (Bx4-03 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ02 ∷ []) (refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 0 3 (CZ03 ∷ []) (by-assoc Eq.refl) ▸
       at 0 1 (Bx4-03 ∷ []) (refl) ▸ done


-- comm push BOX(0;412) sw2 R: 8 steps
lem-comm-push-BOX⟨0·412⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Bx0-412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-413 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·412⟩-sw2-R c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-412 ∷ []) (Bx0-413 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff014 ∷ Bx4-02 ∷ Toff014 ∷ CCZ014 ∷ Bx4-02 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw23 ∷ []) (lem-comm-push-CCZ014-sw2-R c4) ▸
       at 1 2 (Toff014 ∷ Sw23 ∷ []) (lem-comm-push-TOFF014-sw2-R c4) ▸
       at 2 2 (Bx4-03 ∷ Sw23 ∷ []) (lem-comm-push-BOX⟨4·02⟩-sw2-R c4) ▸
       at 3 2 (Toff014 ∷ Sw23 ∷ []) (lem-comm-push-TOFF014-sw2-R c4) ▸
       at 4 2 (CCZ014 ∷ Sw23 ∷ []) (lem-comm-push-CCZ014-sw2-R c4) ▸
       at 5 2 (Bx4-03 ∷ Sw23 ∷ []) (lem-comm-push-BOX⟨4·02⟩-sw2-R c4) ▸
       at 0 6 (Bx0-413 ∷ []) (refl) ▸ done


-- comm push BOX(4;0312) sw2 R: 12 steps
lem-comm-push-BOX⟨4·0312⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Bx4-0312 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0213 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨4·0312⟩-sw2-R c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw23 ∷ Bx4-0312 ∷ []) (CCZ024 ∷ Toff402 ∷ Bx0-413 ∷ Toff402 ∷ Sw23 ∷ CCZ034 ∷ Bx0-412 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff403 ∷ Bx0-412 ∷ Toff403 ∷ CCZ034 ∷ Bx0-412 ∷ []) (refl) ▸
       at 1 1 (Sw23 ∷ CCZ024 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0003 c4) ▸
       at 2 1 (Sw23 ∷ Toff402 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0003 c4) ▸
       at 2 2 (Bx0-413 ∷ Sw23 ∷ []) (lem-comm-push-BOX⟨0·412⟩-sw2-R c4) ▸
       at 4 1 (Sw23 ∷ Toff402 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0003 c4) ▸ done

  b1 : Chain (CCZ024 ∷ Toff402 ∷ Bx0-413 ∷ Toff402 ∷ Sw23 ∷ CCZ034 ∷ Bx0-412 ∷ []) (Bx4-0213 ∷ Sw23 ∷ [])
  b1 = at 5 1 (Sw23 ∷ CCZ024 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0003 c4) ▸
       at 5 2 (Bx0-413 ∷ Sw23 ∷ []) (lem-comm-push-BOX⟨0·412⟩-sw2-R c4) ▸
       at 0 6 (Bx4-0213 ∷ []) (refl) ▸ done


-- comm push SBOX(4;0;2;1) sw2 R: 4 steps
lem-comm-push-SBOX⟨4·0·2·1⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Sb4-0-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-0-3-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨4·0·2·1⟩-sw2-R c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb4-0-2-1 ∷ []) (Sb4-0-3-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS02 ∷ []) (refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 0 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 0 1 (Sb4-0-3-1 ∷ []) (refl) ▸ done


-- comm push SBOXd(4;0;2;1) sw2 R: 4 steps
lem-comm-push-SBOXd⟨4·0·2·1⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Sb⁻4-0-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-0-3-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨4·0·2·1⟩-sw2-R c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻4-0-2-1 ∷ []) (Sb⁻4-0-3-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS02⁻ ∷ []) (refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 0 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 0 1 (Sb⁻4-0-3-1 ∷ []) (refl) ▸ done


-- comm push SBOX(4;0;31;2) sw2 R: 7 steps
lem-comm-push-SBOX⟨4·0·31·2⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Sb4-0-31-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-0-21-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨4·0·31·2⟩-sw2-R c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb4-0-31-2 ∷ []) (Sb4-0-21-3 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx4-0312 ∷ Toff213 ∷ Sb4-0-2-1 ∷ Toff213 ∷ Sb⁻4-0-2-1 ∷ []) (refl) ▸
       at 0 2 (Bx4-0213 ∷ Sw23 ∷ []) (lem-comm-push-BOX⟨4·0312⟩-sw2-R c4) ▸
       at 1 2 (Toff312 ∷ Sw23 ∷ []) (wl0126 c4) ▸
       at 2 2 (Sb4-0-3-1 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨4·0·2·1⟩-sw2-R c4) ▸
       at 3 2 (Toff312 ∷ Sw23 ∷ []) (wl0126 c4) ▸
       at 4 2 (Sb⁻4-0-3-1 ∷ Sw23 ∷ []) (lem-comm-push-SBOXd⟨4·0·2·1⟩-sw2-R c4) ▸
       at 0 5 (Sb4-0-21-3 ∷ []) (refl) ▸ done


-- comm push BOX(4;03) sw1 R: 3 steps
lem-comm-push-BOX⟨4·03⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Bx4-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-03 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨4·03⟩-sw1-R c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-03 ∷ []) (Bx4-03 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ03 ∷ []) (refl) ▸
       at 0 2 (CZ03 ∷ Sw12 ∷ []) (sym (wl0079 c4)) ▸
       at 0 1 (Bx4-03 ∷ []) (refl) ▸ done


-- comm push BOX(0;413) sw1 R: 12 steps
lem-comm-push-BOX⟨0·413⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Bx0-413 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-423 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·413⟩-sw1-R c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw12 ∷ Bx0-413 ∷ []) (CCZ024 ∷ Toff024 ∷ Bx4-03 ∷ Toff024 ∷ Sw12 ∷ CCZ014 ∷ Bx4-03 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff014 ∷ Bx4-03 ∷ Toff014 ∷ CCZ014 ∷ Bx4-03 ∷ []) (refl) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 0 3 (CCZ024 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 1 3 (Toff024 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Bx4-03 ∷ Sw12 ∷ []) (lem-comm-push-BOX⟨4·03⟩-sw1-R c4) ▸
       at 5 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 3 3 (Toff024 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff024 ∷ Bx4-03 ∷ Toff024 ∷ Sw12 ∷ CCZ014 ∷ Bx4-03 ∷ []) (Bx0-423 ∷ Sw12 ∷ [])
  b1 = at 6 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 4 3 (CCZ024 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Bx4-03 ∷ Sw12 ∷ []) (lem-comm-push-BOX⟨4·03⟩-sw1-R c4) ▸
       at 0 6 (Bx0-423 ∷ []) (refl) ▸ done


-- comm push BOX(4;0213) sw1 R: 12 steps
lem-comm-push-BOX⟨4·0213⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Bx4-0213 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0123 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨4·0213⟩-sw1-R c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw12 ∷ Bx4-0213 ∷ []) (CCZ014 ∷ Toff401 ∷ Bx0-423 ∷ Toff401 ∷ Sw12 ∷ CCZ024 ∷ Bx0-413 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff402 ∷ Bx0-413 ∷ Toff402 ∷ CCZ024 ∷ Bx0-413 ∷ []) (refl) ▸
       at 1 1 (Sw12 ∷ CCZ014 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0006 c4) ▸
       at 2 1 (Sw12 ∷ Toff401 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0006 c4) ▸
       at 2 2 (Bx0-423 ∷ Sw12 ∷ []) (lem-comm-push-BOX⟨0·413⟩-sw1-R c4) ▸
       at 4 1 (Sw12 ∷ Toff401 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0006 c4) ▸ done

  b1 : Chain (CCZ014 ∷ Toff401 ∷ Bx0-423 ∷ Toff401 ∷ Sw12 ∷ CCZ024 ∷ Bx0-413 ∷ []) (Bx4-0123 ∷ Sw12 ∷ [])
  b1 = at 5 1 (Sw12 ∷ CCZ014 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0006 c4) ▸
       at 5 2 (Bx0-423 ∷ Sw12 ∷ []) (lem-comm-push-BOX⟨0·413⟩-sw1-R c4) ▸
       at 0 6 (Bx4-0123 ∷ []) (refl) ▸ done


-- comm push SBOX(4;0;3;1) sw1 R: 3 steps
lem-comm-push-SBOX⟨4·0·3·1⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Sb4-0-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-0-3-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨4·0·3·1⟩-sw1-R c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb4-0-3-1 ∷ []) (Sb4-0-3-2 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS03 ∷ []) (refl) ▸
       at 0 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 0 1 (Sb4-0-3-2 ∷ []) (refl) ▸ done


-- comm push SBOXd(4;0;3;1) sw1 R: 3 steps
lem-comm-push-SBOXd⟨4·0·3·1⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Sb⁻4-0-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-0-3-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨4·0·3·1⟩-sw1-R c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻4-0-3-1 ∷ []) (Sb⁻4-0-3-2 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 2 (CS03⁻ ∷ Sw12 ∷ []) (sym (wl0043 c4)) ▸
       at 0 1 (Sb⁻4-0-3-2 ∷ []) (refl) ▸ done


-- comm push SBOX(4;0;21;3) sw1 R: 7 steps
lem-comm-push-SBOX⟨4·0·21·3⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Sb4-0-21-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-0-12-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨4·0·21·3⟩-sw1-R c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb4-0-21-3 ∷ []) (Sb4-0-12-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx4-0213 ∷ Toff312 ∷ Sb4-0-3-1 ∷ Toff312 ∷ Sb⁻4-0-3-1 ∷ []) (refl) ▸
       at 0 2 (Bx4-0123 ∷ Sw12 ∷ []) (lem-comm-push-BOX⟨4·0213⟩-sw1-R c4) ▸
       at 1 2 (Toff312 ∷ Sw12 ∷ []) (wl0150 c4) ▸
       at 2 2 (Sb4-0-3-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨4·0·3·1⟩-sw1-R c4) ▸
       at 3 2 (Toff312 ∷ Sw12 ∷ []) (wl0150 c4) ▸
       at 4 2 (Sb⁻4-0-3-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOXd⟨4·0·3·1⟩-sw1-R c4) ▸
       at 0 5 (Sb4-0-12-3 ∷ []) (refl) ▸ done


-- comm push BOX(4;03) sw0 R: 3 steps
lem-comm-push-BOX⟨4·03⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Bx4-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-13 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨4·03⟩-sw0-R c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-03 ∷ []) (Bx4-13 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ03 ∷ []) (refl) ▸
       at 0 2 (CZ13 ∷ Sw01 ∷ []) (sym (wl0151 c4)) ▸
       at 0 1 (Bx4-13 ∷ []) (refl) ▸ done


-- comm push BOX(0;423) sw0 R: 8 steps
lem-comm-push-BOX⟨0·423⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Bx0-423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-423 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·423⟩-sw0-R c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-423 ∷ []) (Bx1-423 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx4-03 ∷ Toff024 ∷ CCZ024 ∷ Bx4-03 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw01 ∷ []) (lem-comm-push-CCZ024-sw0-R c4) ▸
       at 1 2 (Toff124 ∷ Sw01 ∷ []) (lem-comm-push-TOFF024-sw0-R c4) ▸
       at 2 2 (Bx4-13 ∷ Sw01 ∷ []) (lem-comm-push-BOX⟨4·03⟩-sw0-R c4) ▸
       at 3 2 (Toff124 ∷ Sw01 ∷ []) (lem-comm-push-TOFF024-sw0-R c4) ▸
       at 4 2 (CCZ124 ∷ Sw01 ∷ []) (lem-comm-push-CCZ024-sw0-R c4) ▸
       at 5 2 (Bx4-13 ∷ Sw01 ∷ []) (lem-comm-push-BOX⟨4·03⟩-sw0-R c4) ▸
       at 0 6 (Bx1-423 ∷ []) (refl) ▸ done


-- comm push BOX(4;0123) sw0 R: 8 steps
lem-comm-push-BOX⟨4·0123⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Bx4-0123 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1023 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨4·0123⟩-sw0-R c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-0123 ∷ []) (Bx4-1023 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff401 ∷ Bx0-423 ∷ Toff401 ∷ CCZ014 ∷ Bx0-423 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw01 ∷ []) (lem-comm-push-CCZ014-sw0-R c4) ▸
       at 1 2 (Toff401 ∷ Sw01 ∷ []) (lem-comm-push-TOFF401-sw0-R c4) ▸
       at 2 2 (Bx1-423 ∷ Sw01 ∷ []) (lem-comm-push-BOX⟨0·423⟩-sw0-R c4) ▸
       at 3 2 (Toff401 ∷ Sw01 ∷ []) (lem-comm-push-TOFF401-sw0-R c4) ▸
       at 4 2 (CCZ014 ∷ Sw01 ∷ []) (lem-comm-push-CCZ014-sw0-R c4) ▸
       at 5 2 (Bx1-423 ∷ Sw01 ∷ []) (lem-comm-push-BOX⟨0·423⟩-sw0-R c4) ▸
       at 0 6 (Bx4-1023 ∷ []) (refl) ▸ done


-- comm push SBOX(4;0;3;2) sw0 R: 3 steps
lem-comm-push-SBOX⟨4·0·3·2⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Sb4-0-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-1-3-2 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨4·0·3·2⟩-sw0-R c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb4-0-3-2 ∷ []) (Sb4-1-3-2 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS03 ∷ []) (refl) ▸
       at 0 2 (CS13 ∷ Sw01 ∷ []) (sym (wl0106 c4)) ▸
       at 0 1 (Sb4-1-3-2 ∷ []) (refl) ▸ done


-- comm push SBOXd(4;0;3;2) sw0 R: 3 steps
lem-comm-push-SBOXd⟨4·0·3·2⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Sb⁻4-0-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-1-3-2 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨4·0·3·2⟩-sw0-R c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻4-0-3-2 ∷ []) (Sb⁻4-1-3-2 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 2 (CS13⁻ ∷ Sw01 ∷ []) (sym (wl0105 c4)) ▸
       at 0 1 (Sb⁻4-1-3-2 ∷ []) (refl) ▸ done


-- comm push SBOX(4;0;12;3) sw0 R: 7 steps
lem-comm-push-SBOX⟨4·0·12·3⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Sb4-0-12-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-1-02-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨4·0·12·3⟩-sw0-R c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb4-0-12-3 ∷ []) (Sb4-1-02-3 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx4-0123 ∷ Toff312 ∷ Sb4-0-3-2 ∷ Toff312 ∷ Sb⁻4-0-3-2 ∷ []) (refl) ▸
       at 0 2 (Bx4-1023 ∷ Sw01 ∷ []) (lem-comm-push-BOX⟨4·0123⟩-sw0-R c4) ▸
       at 1 2 (Toff302 ∷ Sw01 ∷ []) (wl0063 c4) ▸
       at 2 2 (Sb4-1-3-2 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨4·0·3·2⟩-sw0-R c4) ▸
       at 3 2 (Toff302 ∷ Sw01 ∷ []) (wl0063 c4) ▸
       at 4 2 (Sb⁻4-1-3-2 ∷ Sw01 ∷ []) (lem-comm-push-SBOXd⟨4·0·3·2⟩-sw0-R c4) ▸
       at 0 5 (Sb4-1-02-3 ∷ []) (refl) ▸ done


-- comm SWAP12 BOX(4;03): 11 steps
lem-comm-SWAP12-BOX⟨4·03⟩ : WsL → ⟪ (Sw12 ∷ Bx4-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-03 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-SWAP12-BOX⟨4·03⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw12 ∷ Bx4-03 ∷ []) (Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ03 ∷ []) (refl) ▸
       at 1 1 (Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (Sw13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw12 ∷ Sw23 ∷ []) (sym (wl0075 c4)) ▸
       at 2 2 (CZ01 ∷ Sw23 ∷ []) (sym (c₂ (CZ) (Swap))) ▸
       at 3 2 (Sw12 ∷ Sw13 ∷ []) (sym (wl0096 c4)) ▸
       at 4 1 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ []) (Bx4-03 ∷ Sw12 ∷ [])
  b1 = at 6 2 [] (wl0003 c4) ▸
       at 0 5 (CZ03 ∷ []) (by-assoc Eq.refl) ▸
       at 0 1 (Bx4-03 ∷ []) (refl) ▸ done


-- resp CZ03 at 2: 4 steps
lem-resp-CZ03-at-2 : WsL → ⟪ (CZ03 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CZ13 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CZ03-at-2 c4 = run b0
  where
  b0 : Chain (CZ03 ∷ []) (Sw12 ∷ Sw01 ∷ CZ13 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 0 2 (Sw12 ∷ CZ03 ∷ []) (wl0079 c4) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 1 2 (Sw01 ∷ CZ13 ∷ []) (wl0049 c4) ▸ done


-- comm CZ13 TOFF402: 11 steps
lem-comm-CZ13-TOFF402 : WsL → ⟪ (CZ13 ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ CZ13 ∷ []) ⟫ʷ
lem-comm-CZ13-TOFF402 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CZ13 ∷ Toff402 ∷ []) (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ CZ23 ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ CZ23 ∷ []) (wl0033 c4) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 3 (CZ24 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw23 ∷ CZ34 ∷ []) (wl0034 c4) ▸
       at 3 2 (Toff201 ∷ CZ34 ∷ []) (sym (c₃ (Toffᵗ) (CZ))) ▸
       at 4 2 (Sw23 ∷ CZ24 ∷ []) (wl0035 c4) ▸
       at 5 1 (Sw34 ∷ CZ23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ CZ23 ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ []) (Toff402 ∷ CZ13 ∷ [])
  b1 = at 7 2 [] (wl0004 c4) ▸
       at 6 2 (Sw12 ∷ CZ13 ∷ []) (wl0036 c4) ▸
       at 0 7 (Toff402 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm TOFF413 CSd02: 23 steps
lem-comm-TOFF413-CSd02 : WsL → ⟪ (Toff413 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ Toff413 ∷ []) ⟫ʷ
lem-comm-TOFF413-CSd02 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Toff413 ∷ CS02⁻ ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Toff412 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Sw34 ∷ Toff312 ∷ Sw34 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (CS04⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (Toff412 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Toff412 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Toff312 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b1 = at 3 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (Toff413 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw12 ∷ Toff423 ∷ []) (sym (wl0085 c4)) ▸
       at 5 2 (CS01⁻ ∷ Toff423 ∷ []) (sym (c₂ (CS • CS • CS) (Toffᵗ))) ▸
       at 6 2 (Sw12 ∷ Toff413 ∷ []) (sym (wl0084 c4)) ▸
       at 7 1 (Sw23 ∷ Toff412 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (wl0003 c4) ▸
       at 8 1 (Sw34 ∷ Toff312 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Toff312 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (CS02⁻ ∷ Toff413 ∷ [])
  b2 = at 10 2 [] (wl0004 c4) ▸
       at 2 7 (CS04⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ CS03⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0004 c4) ▸
       at 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0003 c4) ▸
       at 1 5 (Toff413 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CCZ134 CK02: 23 steps
lem-comm-CCZ134-CK02 : WsL → ⟪ (CCZ134 ∷ CK02 ∷ []) ⟫ʷ ≈ ⟪ (CK02 ∷ CCZ134 ∷ []) ⟫ʷ
lem-comm-CCZ134-CK02 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CCZ134 ∷ CK02 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ CCZ124 ∷ Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (CK03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (CK04 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (CCZ124 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ CCZ124 ∷ Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b1 = at 3 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw12 ∷ CCZ234 ∷ []) (wl0037 c4) ▸
       at 5 2 (CK01 ∷ CCZ234 ∷ []) (sym (c₂ (CK₀₁) (CCZ))) ▸
       at 6 2 (Sw12 ∷ CCZ134 ∷ []) (wl0044 c4) ▸
       at 7 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (wl0003 c4) ▸
       at 8 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (CK02 ∷ CCZ134 ∷ [])
  b2 = at 10 2 [] (wl0004 c4) ▸
       at 2 7 (CK04 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ CK03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0004 c4) ▸
       at 1 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0003 c4) ▸
       at 1 5 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CX23 TOFF401: 9 steps
lem-comm-CX23-TOFF401 : WsL → ⟪ (CX23 ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ CX23 ∷ []) ⟫ʷ
lem-comm-CX23-TOFF401 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX23 ∷ Toff401 ∷ []) (Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ CX23 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 3 (CX24 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw23 ∷ CX34 ∷ []) (wl0020 c4) ▸
       at 2 2 (Toff201 ∷ CX34 ∷ []) (sym (c₃ (Toffᵗ) (CX₀₁))) ▸
       at 3 2 (Sw23 ∷ CX24 ∷ []) (wl0021 c4) ▸
       at 4 1 (Sw34 ∷ CX23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0004 c4) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ CX23 ∷ []) (Toff401 ∷ CX23 ∷ [])
  b1 = at 0 5 (Toff401 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CZ23 TOFF401: 9 steps
lem-comm-CZ23-TOFF401 : WsL → ⟪ (CZ23 ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ CZ23 ∷ []) ⟫ʷ
lem-comm-CZ23-TOFF401 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CZ23 ∷ Toff401 ∷ []) (Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ CZ23 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 3 (CZ24 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw23 ∷ CZ34 ∷ []) (wl0034 c4) ▸
       at 2 2 (Toff201 ∷ CZ34 ∷ []) (sym (c₃ (Toffᵗ) (CZ))) ▸
       at 3 2 (Sw23 ∷ CZ24 ∷ []) (wl0035 c4) ▸
       at 4 1 (Sw34 ∷ CZ23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0004 c4) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ CZ23 ∷ []) (Toff401 ∷ CZ23 ∷ [])
  b1 = at 0 5 (Toff401 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CK02 CCZ134: 23 steps
lem-comm-CK02-CCZ134 : WsL → ⟪ (CK02 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CK02 ∷ []) ⟫ʷ
lem-comm-CK02-CCZ134 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CK02 ∷ CCZ134 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ CCZ124 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (CK03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 3 (CK04 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 8 3 (CCZ124 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ CCZ124 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b1 = at 9 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 7 3 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0044 c4)) ▸
       at 5 2 (CCZ234 ∷ CK01 ∷ []) (c₂ (CK₀₁) (CCZ)) ▸
       at 4 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 4 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0003 c4) ▸
       at 3 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (CCZ134 ∷ CK02 ∷ [])
  b2 = at 2 2 [] (wl0004 c4) ▸
       at 3 7 (CK04 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ CK03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0004 c4) ▸
       at 4 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0003 c4) ▸
       at 0 5 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm TOFF413 CK02: 23 steps
lem-comm-TOFF413-CK02 : WsL → ⟪ (Toff413 ∷ CK02 ∷ []) ⟫ʷ ≈ ⟪ (CK02 ∷ Toff413 ∷ []) ⟫ʷ
lem-comm-TOFF413-CK02 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Toff413 ∷ CK02 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Toff412 ∷ Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Sw34 ∷ Toff312 ∷ Sw34 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (CK03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (CK04 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (Toff412 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Toff412 ∷ Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Toff312 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b1 = at 3 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (Toff413 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw12 ∷ Toff423 ∷ []) (sym (wl0085 c4)) ▸
       at 5 2 (CK01 ∷ Toff423 ∷ []) (sym (c₂ (CK₀₁) (Toffᵗ))) ▸
       at 6 2 (Sw12 ∷ Toff413 ∷ []) (sym (wl0084 c4)) ▸
       at 7 1 (Sw23 ∷ Toff412 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (wl0003 c4) ▸
       at 8 1 (Sw34 ∷ Toff312 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Toff312 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (CK02 ∷ Toff413 ∷ [])
  b2 = at 10 2 [] (wl0004 c4) ▸
       at 2 7 (CK04 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ CK03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0004 c4) ▸
       at 1 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0003 c4) ▸
       at 1 5 (Toff413 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm TOFF401 CX23: 9 steps
lem-comm-TOFF401-CX23 : WsL → ⟪ (Toff401 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ Toff401 ∷ []) ⟫ʷ
lem-comm-TOFF401-CX23 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff401 ∷ CX23 ∷ []) (CX23 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 4 3 (CX24 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX34 ∷ Sw23 ∷ []) (sym (wl0021 c4)) ▸
       at 2 2 (CX34 ∷ Toff201 ∷ []) (c₃ (Toffᵗ) (CX₀₁)) ▸
       at 1 2 (CX24 ∷ Sw23 ∷ []) (sym (wl0020 c4)) ▸
       at 1 1 (Sw34 ∷ CX23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0004 c4) ▸ done

  b1 : Chain (CX23 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ []) (CX23 ∷ Toff401 ∷ [])
  b1 = at 1 5 (Toff401 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CX20 TOFF413: 23 steps
lem-comm-CX20-TOFF413 : WsL → ⟪ (CX20 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CX20 ∷ []) ⟫ʷ
lem-comm-CX20-TOFF413 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX20 ∷ Toff413 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Toff412 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw34 ∷ Toff312 ∷ Sw34 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 3 (CX40 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 8 3 (Toff412 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Toff412 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Toff312 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b1 = at 9 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 7 3 (Toff413 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Toff423 ∷ Sw12 ∷ []) (wl0084 c4) ▸
       at 5 2 (Toff423 ∷ CX10 ∷ []) (c₂ (CX₁₀) (Toffᵗ)) ▸
       at 4 2 (Toff413 ∷ Sw12 ∷ []) (wl0085 c4) ▸
       at 4 1 (Sw23 ∷ Toff412 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0003 c4) ▸
       at 3 1 (Sw34 ∷ Toff312 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Toff312 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (Toff413 ∷ CX20 ∷ [])
  b2 = at 2 2 [] (wl0004 c4) ▸
       at 3 7 (CX40 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ CX30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0004 c4) ▸
       at 4 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0003 c4) ▸
       at 0 5 (Toff413 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm TOFF413 CX20: 23 steps
lem-comm-TOFF413-CX20 : WsL → ⟪ (Toff413 ∷ CX20 ∷ []) ⟫ʷ ≈ ⟪ (CX20 ∷ Toff413 ∷ []) ⟫ʷ
lem-comm-TOFF413-CX20 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Toff413 ∷ CX20 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Toff412 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Sw34 ∷ Toff312 ∷ Sw34 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (CX40 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (Toff412 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Toff412 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Toff312 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b1 = at 3 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (Toff413 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw12 ∷ Toff423 ∷ []) (sym (wl0085 c4)) ▸
       at 5 2 (CX10 ∷ Toff423 ∷ []) (sym (c₂ (CX₁₀) (Toffᵗ))) ▸
       at 6 2 (Sw12 ∷ Toff413 ∷ []) (sym (wl0084 c4)) ▸
       at 7 1 (Sw23 ∷ Toff412 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (wl0003 c4) ▸
       at 8 1 (Sw34 ∷ Toff312 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Toff312 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (CX20 ∷ Toff413 ∷ [])
  b2 = at 10 2 [] (wl0004 c4) ▸
       at 2 7 (CX40 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ CX30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0004 c4) ▸
       at 1 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0003 c4) ▸
       at 1 5 (Toff413 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CK03 CCZ124: 9 steps
lem-comm-CK03-CCZ124 : WsL → ⟪ (CK03 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CK03 ∷ []) ⟫ʷ
lem-comm-CK03-CCZ124 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CK03 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0044 c4)) ▸
       at 2 2 (CCZ234 ∷ CK01 ∷ []) (c₂ (CK₀₁) (CCZ)) ▸
       at 1 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 1 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0003 c4) ▸ done

  b1 : Chain (CCZ124 ∷ Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) (CCZ124 ∷ CK03 ∷ [])
  b1 = at 1 5 (CK03 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CK03 at 1: 2 steps
lem-resp-CK03-at-1 : WsL → ⟪ (CK03 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CK13 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CK03-at-1 c4 = run b0
  where
  b0 : Chain (CK03 ∷ []) (Sw01 ∷ CK13 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 0 2 (Sw01 ∷ CK13 ∷ []) (wl0152 c4) ▸ done


-- comm TOFF403 CSd12: 15 steps
lem-comm-TOFF403-CSd12 : WsL → ⟪ (Toff403 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ Toff403 ∷ []) ⟫ʷ
lem-comm-TOFF403-CSd12 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff403 ∷ CS12⁻ ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CS34⁻ ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 8 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CS23⁻ ∷ Sw12 ∷ []) (sym (wl0029 c4)) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 6 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0009 c4)) ▸
       at 4 2 (CS34⁻ ∷ Toff201 ∷ []) (c₃ (Toffᵗ) (CS • CS • CS)) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CS34⁻ ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (CS12⁻ ∷ Toff403 ∷ [])
  b1 = at 3 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0012 c4)) ▸
       at 3 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0004 c4) ▸
       at 1 2 (CS13⁻ ∷ Sw12 ∷ []) (sym (wl0028 c4)) ▸
       at 1 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0003 c4) ▸
       at 1 9 (Toff403 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CCZ124 CK03: 9 steps
lem-comm-CCZ124-CK03 : WsL → ⟪ (CCZ124 ∷ CK03 ∷ []) ⟫ʷ ≈ ⟪ (CK03 ∷ CCZ124 ∷ []) ⟫ʷ
lem-comm-CCZ124-CK03 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ124 ∷ CK03 ∷ []) (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ CCZ124 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw12 ∷ CCZ234 ∷ []) (wl0037 c4) ▸
       at 2 2 (CK01 ∷ CCZ234 ∷ []) (sym (c₂ (CK₀₁) (CCZ))) ▸
       at 3 2 (Sw12 ∷ CCZ134 ∷ []) (wl0044 c4) ▸
       at 4 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0003 c4) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ CCZ124 ∷ []) (CK03 ∷ CCZ124 ∷ [])
  b1 = at 0 5 (CK03 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CS02 TOFF413: 23 steps
lem-comm-CS02-TOFF413 : WsL → ⟪ (CS02 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CS02 ∷ []) ⟫ʷ
lem-comm-CS02-TOFF413 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS02 ∷ Toff413 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Toff412 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw34 ∷ Toff312 ∷ Sw34 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 8 3 (Toff412 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Toff412 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Toff312 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b1 = at 9 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 7 3 (Toff413 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Toff423 ∷ Sw12 ∷ []) (wl0084 c4) ▸
       at 5 2 (Toff423 ∷ CS01 ∷ []) (c₂ (CS) (Toffᵗ)) ▸
       at 4 2 (Toff413 ∷ Sw12 ∷ []) (wl0085 c4) ▸
       at 4 1 (Sw23 ∷ Toff412 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0003 c4) ▸
       at 3 1 (Sw34 ∷ Toff312 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Toff312 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (Toff413 ∷ CS02 ∷ [])
  b2 = at 2 2 [] (wl0004 c4) ▸
       at 3 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0004 c4) ▸
       at 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0003 c4) ▸
       at 0 5 (Toff413 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CS12 TOFF403: 15 steps
lem-comm-CS12-TOFF403 : WsL → ⟪ (CS12 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CS12 ∷ []) ⟫ʷ
lem-comm-CS12-TOFF403 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS12 ∷ Toff403 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ CS34 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw12 ∷ CS23 ∷ []) (wl0046 c4) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (CS24 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw23 ∷ CS34 ∷ []) (wl0011 c4) ▸
       at 4 2 (Toff201 ∷ CS34 ∷ []) (sym (c₃ (Toffᵗ) (CS))) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ CS34 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Toff403 ∷ CS12 ∷ [])
  b1 = at 5 2 (Sw23 ∷ CS24 ∷ []) (wl0008 c4) ▸
       at 6 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0004 c4) ▸
       at 7 2 (Sw12 ∷ CS13 ∷ []) (wl0047 c4) ▸
       at 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (wl0003 c4) ▸
       at 0 9 (Toff403 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CX41 TOFF203: 7 steps
lem-comm-CX41-TOFF203 : WsL → ⟪ (CX41 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CX41 ∷ []) ⟫ʷ
lem-comm-CX41-TOFF203 c4 = run b0
  where
  b0 : Chain (CX41 ∷ Toff203 ∷ []) (Toff203 ∷ CX41 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ CX42 ∷ []) (wl0069 c4) ▸
       at 1 2 (Sw23 ∷ CX43 ∷ []) (wl0058 c4) ▸
       at 2 2 (Toff102 ∷ CX43 ∷ []) (sym (c₃ (K ↑ • CCZ • K ↑ • iI) (CX₁₀))) ▸
       at 3 2 (Sw23 ∷ CX42 ∷ []) (wl0059 c4) ▸
       at 4 2 (Sw12 ∷ CX41 ∷ []) (wl0089 c4) ▸
       at 0 5 (Toff203 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CZ02 TOFF413: 23 steps
lem-comm-CZ02-TOFF413 : WsL → ⟪ (CZ02 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CZ02 ∷ []) ⟫ʷ
lem-comm-CZ02-TOFF413 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CZ02 ∷ Toff413 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Toff412 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw34 ∷ Toff312 ∷ Sw34 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (CZ03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 3 (CZ04 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 8 3 (Toff412 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Toff412 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Toff312 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b1 = at 9 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 7 3 (Toff413 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Toff423 ∷ Sw12 ∷ []) (wl0084 c4) ▸
       at 5 2 (Toff423 ∷ CZ01 ∷ []) (c₂ (CZ) (Toffᵗ)) ▸
       at 4 2 (Toff413 ∷ Sw12 ∷ []) (wl0085 c4) ▸
       at 4 1 (Sw23 ∷ Toff412 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0003 c4) ▸
       at 3 1 (Sw34 ∷ Toff312 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Toff312 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (Toff413 ∷ CZ02 ∷ [])
  b2 = at 2 2 [] (wl0004 c4) ▸
       at 3 7 (CZ04 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ CZ03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0004 c4) ▸
       at 4 1 (Sw23 ∷ CZ02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0003 c4) ▸
       at 0 5 (Toff413 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm TOFF413 CS02: 23 steps
lem-comm-TOFF413-CS02 : WsL → ⟪ (Toff413 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ Toff413 ∷ []) ⟫ʷ
lem-comm-TOFF413-CS02 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Toff413 ∷ CS02 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Toff412 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Sw34 ∷ Toff312 ∷ Sw34 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (Toff412 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Toff412 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Toff312 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b1 = at 3 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (Toff413 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw12 ∷ Toff423 ∷ []) (sym (wl0085 c4)) ▸
       at 5 2 (CS01 ∷ Toff423 ∷ []) (sym (c₂ (CS) (Toffᵗ))) ▸
       at 6 2 (Sw12 ∷ Toff413 ∷ []) (sym (wl0084 c4)) ▸
       at 7 1 (Sw23 ∷ Toff412 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (wl0003 c4) ▸
       at 8 1 (Sw34 ∷ Toff312 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Toff312 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (CS02 ∷ Toff413 ∷ [])
  b2 = at 10 2 [] (wl0004 c4) ▸
       at 2 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0004 c4) ▸
       at 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0003 c4) ▸
       at 1 5 (Toff413 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CK02 at 1: 2 steps
lem-resp-CK02-at-1 : WsL → ⟪ (CK02 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CK12 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CK02-at-1 c4 = run b0
  where
  b0 : Chain (CK02 ∷ []) (Sw01 ∷ CK12 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 0 2 (Sw01 ∷ CK12 ∷ []) (wl0153 c4) ▸ done


-- comm SWAP13 BOX(4;20): 7 steps
lem-comm-SWAP13-BOX⟨4·20⟩ : WsL → ⟪ (Sw13 ∷ Bx4-20 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-20 ∷ Sw13 ∷ []) ⟫ʷ
lem-comm-SWAP13-BOX⟨4·20⟩ c4 = run b0
  where
  b0 : Chain (Sw13 ∷ Bx4-20 ∷ []) (Bx4-20 ∷ Sw13 ∷ [])
  b0 = at 1 1 (CZ02 ∷ []) (refl) ▸
       at 1 1 (Sw12 ∷ CZ01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ Sw23 ∷ []) (sym (wl0075 c4)) ▸
       at 1 2 (CZ01 ∷ Sw23 ∷ []) (sym (c₂ (CZ) (Swap))) ▸
       at 2 2 (Sw12 ∷ Sw13 ∷ []) (sym (wl0096 c4)) ▸
       at 0 3 (CZ02 ∷ []) (by-assoc Eq.refl) ▸
       at 0 1 (Bx4-20 ∷ []) (refl) ▸ done


-- comm CX41 TOFF302: 7 steps
lem-comm-CX41-TOFF302 : WsL → ⟪ (CX41 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CX41 ∷ []) ⟫ʷ
lem-comm-CX41-TOFF302 c4 = run b0
  where
  b0 : Chain (CX41 ∷ Toff302 ∷ []) (Toff302 ∷ CX41 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ CX42 ∷ []) (wl0069 c4) ▸
       at 1 2 (Sw23 ∷ CX43 ∷ []) (wl0058 c4) ▸
       at 2 2 (Toff201 ∷ CX43 ∷ []) (sym (c₃ (Toffᵗ) (CX₁₀))) ▸
       at 3 2 (Sw23 ∷ CX42 ∷ []) (wl0059 c4) ▸
       at 4 2 (Sw12 ∷ CX41 ∷ []) (wl0089 c4) ▸
       at 0 5 (Toff302 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm TOFF403 CX12: 15 steps
lem-comm-TOFF403-CX12 : WsL → ⟪ (Toff403 ∷ CX12 ∷ []) ⟫ʷ ≈ ⟪ (CX12 ∷ Toff403 ∷ []) ⟫ʷ
lem-comm-TOFF403-CX12 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff403 ∷ CX12 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CX34 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 8 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX23 ∷ Sw12 ∷ []) (sym (wl0022 c4)) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 6 3 (CX24 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX34 ∷ Sw23 ∷ []) (sym (wl0021 c4)) ▸
       at 4 2 (CX34 ∷ Toff201 ∷ []) (c₃ (Toffᵗ) (CX₀₁)) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CX34 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (CX12 ∷ Toff403 ∷ [])
  b1 = at 3 2 (CX24 ∷ Sw23 ∷ []) (sym (wl0020 c4)) ▸
       at 3 1 (Sw34 ∷ CX23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0004 c4) ▸
       at 1 2 (CX13 ∷ Sw12 ∷ []) (sym (wl0019 c4)) ▸
       at 1 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0003 c4) ▸
       at 1 9 (Toff403 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CK03 at 2: 4 steps
lem-resp-CK03-at-2 : WsL → ⟪ (CK03 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CK13 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CK03-at-2 c4 = run b0
  where
  b0 : Chain (CK03 ∷ []) (Sw12 ∷ Sw01 ∷ CK13 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 0 2 (Sw12 ∷ CK03 ∷ []) (wl0154 c4) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 1 2 (Sw01 ∷ CK13 ∷ []) (wl0152 c4) ▸ done


-- comm CX21 TOFF403: 15 steps
lem-comm-CX21-TOFF403 : WsL → ⟪ (CX21 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CX21 ∷ []) ⟫ʷ
lem-comm-CX21-TOFF403 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX21 ∷ Toff403 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ CX43 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (CX31 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw12 ∷ CX32 ∷ []) (wl0057 c4) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (CX42 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw23 ∷ CX43 ∷ []) (wl0058 c4) ▸
       at 4 2 (Toff201 ∷ CX43 ∷ []) (sym (c₃ (Toffᵗ) (CX₁₀))) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ CX43 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Toff403 ∷ CX21 ∷ [])
  b1 = at 5 2 (Sw23 ∷ CX42 ∷ []) (wl0059 c4) ▸
       at 6 1 (Sw34 ∷ CX32 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0004 c4) ▸
       at 7 2 (Sw12 ∷ CX31 ∷ []) (wl0060 c4) ▸
       at 8 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (wl0003 c4) ▸
       at 0 9 (Toff403 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CX12 TOFF403: 15 steps
lem-comm-CX12-TOFF403 : WsL → ⟪ (CX12 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CX12 ∷ []) ⟫ʷ
lem-comm-CX12-TOFF403 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX12 ∷ Toff403 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ CX34 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw12 ∷ CX23 ∷ []) (wl0019 c4) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (CX24 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw23 ∷ CX34 ∷ []) (wl0020 c4) ▸
       at 4 2 (Toff201 ∷ CX34 ∷ []) (sym (c₃ (Toffᵗ) (CX₀₁))) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ CX34 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Toff403 ∷ CX12 ∷ [])
  b1 = at 5 2 (Sw23 ∷ CX24 ∷ []) (wl0021 c4) ▸
       at 6 1 (Sw34 ∷ CX23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0004 c4) ▸
       at 7 2 (Sw12 ∷ CX13 ∷ []) (wl0022 c4) ▸
       at 8 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (wl0003 c4) ▸
       at 0 9 (Toff403 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm SWAP12 BOX(4;30): 11 steps
lem-comm-SWAP12-BOX⟨4·30⟩ : WsL → ⟪ (Sw12 ∷ Bx4-30 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-30 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-SWAP12-BOX⟨4·30⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw12 ∷ Bx4-30 ∷ []) (Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ03 ∷ []) (refl) ▸
       at 1 1 (Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (Sw13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw12 ∷ Sw23 ∷ []) (sym (wl0075 c4)) ▸
       at 2 2 (CZ01 ∷ Sw23 ∷ []) (sym (c₂ (CZ) (Swap))) ▸
       at 3 2 (Sw12 ∷ Sw13 ∷ []) (sym (wl0096 c4)) ▸
       at 4 1 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ []) (Bx4-30 ∷ Sw12 ∷ [])
  b1 = at 6 2 [] (wl0003 c4) ▸
       at 0 5 (CZ03 ∷ []) (by-assoc Eq.refl) ▸
       at 0 1 (Bx4-30 ∷ []) (refl) ▸ done


-- comm CX31 TOFF402: 11 steps
lem-comm-CX31-TOFF402 : WsL → ⟪ (CX31 ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ CX31 ∷ []) ⟫ʷ
lem-comm-CX31-TOFF402 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX31 ∷ Toff402 ∷ []) (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ CX32 ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ CX32 ∷ []) (wl0057 c4) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 3 (CX42 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw23 ∷ CX43 ∷ []) (wl0058 c4) ▸
       at 3 2 (Toff201 ∷ CX43 ∷ []) (sym (c₃ (Toffᵗ) (CX₁₀))) ▸
       at 4 2 (Sw23 ∷ CX42 ∷ []) (wl0059 c4) ▸
       at 5 1 (Sw34 ∷ CX32 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ CX32 ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ []) (Toff402 ∷ CX31 ∷ [])
  b1 = at 7 2 [] (wl0004 c4) ▸
       at 6 2 (Sw12 ∷ CX31 ∷ []) (wl0060 c4) ▸
       at 0 7 (Toff402 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm TOFF312 CX40: 13 steps
lem-comm-TOFF312-CX40 : WsL → ⟪ (Toff312 ∷ CX40 ∷ []) ⟫ʷ ≈ ⟪ (CX40 ∷ Toff312 ∷ []) ⟫ʷ
lem-comm-TOFF312-CX40 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff312 ∷ CX40 ∷ []) (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Toff413 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 3 (Toff412 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 2 3 (Toff413 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw12 ∷ Toff423 ∷ []) (sym (wl0085 c4)) ▸
       at 3 2 (CX10 ∷ Toff423 ∷ []) (sym (c₂ (CX₁₀) (Toffᵗ))) ▸
       at 4 2 (Sw12 ∷ Toff413 ∷ []) (sym (wl0084 c4)) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Toff413 ∷ Sw23 ∷ Sw34 ∷ []) (CX40 ∷ Toff312 ∷ [])
  b1 = at 5 1 (Sw23 ∷ Toff412 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0003 c4) ▸
       at 6 1 (Sw34 ∷ Toff312 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0004 c4) ▸
       at 0 7 (CX40 ∷ []) (by-assoc Eq.refl) ▸ done


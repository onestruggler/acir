{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R006 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL ; wl0001 ; wl0003 ; wl0004 ; wl0006 ; wl0008 ; wl0009 ; wl0011 ; wl0012 ; wl0013 ; wl0014 ; wl0015 ; wl0017 ; wl0025 ; wl0038 ; wl0042 ; wl0043 ; wl0045 ; wl0048 ; wl0049 ; wl0058 ; wl0059 ; wl0064 ; wl0065 ; wl0066 ; wl0067 ; wl0072 ; wl0074 ; wl0079 ; wl0081 ; wl0083 ; wl0088 ; wl0093 ; wl0101 ; wl0102 ; wl0103 ; wl0104 ; wl0105 ; wl0106 ; wl0107 ; wl0108 ; wl0109 ; wl0110 ; wl0111 ; wl0112 ; wl0113 ; wl0114 ; wl0115 ; wl0116 ; wl0117 ; wl0118 ; wl0119 ; wl0120 ; wl0121 ; wl0122 ; wl0123 ; wl0124)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-push-CCZ014-sw2-L ; lem-comm-push-CCZ024-sw0-L ; lem-comm-push-CS04-sw0-L ; lem-comm-push-CS04-sw1-R ; lem-comm-push-CS04-sw2-R ; lem-comm-push-TOFF204-sw0-L)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-push-TOFF014-sw2-L)
-- comm SWAP13 BOX(2;04): 13 steps
lem-comm-SWAP13-BOX⟨2·04⟩ : WsL → ⟪ (Sw13 ∷ Bx2-04 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-04 ∷ Sw13 ∷ []) ⟫ʷ
lem-comm-SWAP13-BOX⟨2·04⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw13 ∷ Bx2-04 ∷ []) (Sw34 ∷ Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw14 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ04 ∷ []) (refl) ▸
       at 1 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 3 (Sw14 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw23 ∷ Sw14 ∷ []) (wl0074 c4) ▸
       at 2 2 (Sw12 ∷ Sw24 ∷ []) (sym (wl0072 c4)) ▸
       at 3 2 (CZ01 ∷ Sw24 ∷ []) (sym (c₂ (CZ) (Swap ↑ • Swap • Swap ↑))) ▸
       at 4 2 (Sw12 ∷ Sw14 ∷ []) (sym (wl0093 c4)) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw14 ∷ Sw23 ∷ Sw34 ∷ []) (Bx2-04 ∷ Sw13 ∷ [])
  b1 = at 5 2 (Sw23 ∷ Sw14 ∷ []) (wl0074 c4) ▸
       at 6 1 (Sw34 ∷ Sw13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0004 c4) ▸
       at 0 7 (CZ04 ∷ []) (by-assoc Eq.refl) ▸
       at 0 1 (Bx2-04 ∷ []) (refl) ▸ done


-- comm TOFF214 CX03: 9 steps
lem-comm-TOFF214-CX03 : WsL → ⟪ (Toff214 ∷ CX03 ∷ []) ⟫ʷ ≈ ⟪ (CX03 ∷ Toff214 ∷ []) ⟫ʷ
lem-comm-TOFF214-CX03 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff214 ∷ CX03 ∷ []) (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Toff214 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (Toff314 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw12 ∷ Toff324 ∷ []) (sym (wl0038 c4)) ▸
       at 2 2 (CX01 ∷ Toff324 ∷ []) (sym (c₂ (CX₀₁) (K ↑ • CCZ • K ↑ • iI))) ▸
       at 3 2 (Sw12 ∷ Toff314 ∷ []) (sym (wl0045 c4)) ▸
       at 4 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0003 c4) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Toff214 ∷ []) (CX03 ∷ Toff214 ∷ [])
  b1 = at 0 5 (CX03 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CX32 TOFF014: 9 steps
lem-comm-CX32-TOFF014 : WsL → ⟪ (CX32 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CX32 ∷ []) ⟫ʷ
lem-comm-CX32-TOFF014 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX32 ∷ Toff014 ∷ []) (Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ CX32 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 3 (CX42 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw23 ∷ CX43 ∷ []) (wl0058 c4) ▸
       at 2 2 (Toff012 ∷ CX43 ∷ []) (sym (c₃ (Toff) (CX₁₀))) ▸
       at 3 2 (Sw23 ∷ CX42 ∷ []) (wl0059 c4) ▸
       at 4 1 (Sw34 ∷ CX32 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0004 c4) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ CX32 ∷ []) (Toff014 ∷ CX32 ∷ [])
  b1 = at 0 5 (Toff014 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CCZ013 CS24: 15 steps
lem-comm-CCZ013-CS24 : WsL → ⟪ (CCZ013 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CCZ013 ∷ []) ⟫ʷ
lem-comm-CCZ013-CS24 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ013 ∷ CS24 ∷ []) (Sw34 ∷ Sw34 ∷ Sw23 ∷ CS34 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 3 (CCZ014 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 5 3 (CS24 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0008 c4)) ▸
       at 3 2 (CS34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CS)) ▸ done

  b1 : Chain (Sw34 ∷ Sw34 ∷ Sw23 ∷ CS34 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ []) (CS24 ∷ CCZ013 ∷ [])
  b1 = at 2 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0011 c4)) ▸
       at 2 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0004 c4) ▸
       at 2 5 (CCZ014 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ CCZ013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0004 c4) ▸
       at 0 3 (CS24 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CCZ013 CSd24: 15 steps
lem-comm-CCZ013-CSd24 : WsL → ⟪ (CCZ013 ∷ CS24⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS24⁻ ∷ CCZ013 ∷ []) ⟫ʷ
lem-comm-CCZ013-CSd24 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ013 ∷ CS24⁻ ∷ []) (Sw34 ∷ Sw34 ∷ Sw23 ∷ CS34⁻ ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 3 (CCZ014 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 5 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0009 c4)) ▸
       at 3 2 (CS34⁻ ∷ CCZ012 ∷ []) (c₃ (CCZ) (CS • CS • CS)) ▸ done

  b1 : Chain (Sw34 ∷ Sw34 ∷ Sw23 ∷ CS34⁻ ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ []) (CS24⁻ ∷ CCZ013 ∷ [])
  b1 = at 2 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0012 c4)) ▸
       at 2 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0004 c4) ▸
       at 2 5 (CCZ014 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ CCZ013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0004 c4) ▸
       at 0 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸ done


-- comm push SBOXd(2;0;3;1) sw1 L: 3 steps
lem-comm-push-SBOXd⟨2·0·3·1⟩-sw1-L : WsL → ⟪ (Sb⁻2-0-3-1 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sb⁻1-0-3-2 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨2·0·3·1⟩-sw1-L c4 = run b0
  where
  b0 : Chain (Sb⁻2-0-3-1 ∷ Sw12 ∷ []) (Sw12 ∷ Sb⁻1-0-3-2 ∷ [])
  b0 = at 0 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 2 (Sw12 ∷ CS03⁻ ∷ []) (wl0043 c4) ▸
       at 1 1 (Sb⁻1-0-3-2 ∷ []) (refl) ▸ done


-- comm push SBOX(2;0;3;1) sw1 L: 3 steps
lem-comm-push-SBOX⟨2·0·3·1⟩-sw1-L : WsL → ⟪ (Sb2-0-3-1 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sb1-0-3-2 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨2·0·3·1⟩-sw1-L c4 = run b0
  where
  b0 : Chain (Sb2-0-3-1 ∷ Sw12 ∷ []) (Sw12 ∷ Sb1-0-3-2 ∷ [])
  b0 = at 0 1 (CS03 ∷ []) (refl) ▸
       at 0 2 (Sw12 ∷ CS03 ∷ []) (wl0001 c4) ▸
       at 1 1 (Sb1-0-3-2 ∷ []) (refl) ▸ done


-- comm push BOX(2;03) sw1 L: 3 steps
lem-comm-push-BOX⟨2·03⟩-sw1-L : WsL → ⟪ (Bx2-03 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Bx1-03 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨2·03⟩-sw1-L c4 = run b0
  where
  b0 : Chain (Bx2-03 ∷ Sw12 ∷ []) (Sw12 ∷ Bx1-03 ∷ [])
  b0 = at 0 1 (CZ03 ∷ []) (refl) ▸
       at 0 2 (Sw12 ∷ CZ03 ∷ []) (wl0079 c4) ▸
       at 1 1 (Bx1-03 ∷ []) (refl) ▸ done


-- comm push BOX(0;213) sw1 L: 8 steps
lem-comm-push-BOX⟨0·213⟩-sw1-L : WsL → ⟪ (Bx0-213 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Bx0-123 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·213⟩-sw1-L c4 = run b0
  where
  b0 : Chain (Bx0-213 ∷ Sw12 ∷ []) (Sw12 ∷ Bx0-123 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) (refl) ▸
       at 5 2 (Sw12 ∷ Bx1-03 ∷ []) (lem-comm-push-BOX⟨2·03⟩-sw1-L c4) ▸
       at 4 2 (Sw12 ∷ CCZ012 ∷ []) (wl0101 c4) ▸
       at 3 2 (Sw12 ∷ Toff012 ∷ []) (sym (wl0102 c4)) ▸
       at 2 2 (Sw12 ∷ Bx1-03 ∷ []) (lem-comm-push-BOX⟨2·03⟩-sw1-L c4) ▸
       at 1 2 (Sw12 ∷ Toff012 ∷ []) (sym (wl0102 c4)) ▸
       at 0 2 (Sw12 ∷ CCZ012 ∷ []) (wl0101 c4) ▸
       at 1 6 (Bx0-123 ∷ []) (refl) ▸ done


-- comm push BOX(2;0413) sw1 L: 12 steps
lem-comm-push-BOX⟨2·0413⟩-sw1-L : WsL → ⟪ (Bx2-0413 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨2·0413⟩-sw1-L c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-0413 ∷ Sw12 ∷ []) (CCZ024 ∷ Sw12 ∷ Toff104 ∷ Sw12 ∷ Sw12 ∷ Bx0-123 ∷ Toff104 ∷ CCZ014 ∷ Bx0-123 ∷ [])
  b0 = at 0 1 (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ []) (refl) ▸
       at 5 2 (Sw12 ∷ Bx0-123 ∷ []) (lem-comm-push-BOX⟨0·213⟩-sw1-L c4) ▸
       at 4 1 (Sw12 ∷ CCZ014 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0006 c4) ▸
       at 3 1 (Sw12 ∷ Toff104 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0006 c4) ▸
       at 2 2 (Sw12 ∷ Bx0-123 ∷ []) (lem-comm-push-BOX⟨0·213⟩-sw1-L c4) ▸
       at 1 1 (Sw12 ∷ Toff104 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (CCZ024 ∷ Sw12 ∷ Toff104 ∷ Sw12 ∷ Sw12 ∷ Bx0-123 ∷ Toff104 ∷ CCZ014 ∷ Bx0-123 ∷ []) (Sw12 ∷ Bx1-0423 ∷ [])
  b1 = at 3 2 [] (wl0006 c4) ▸
       at 0 1 (Sw12 ∷ CCZ014 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0006 c4) ▸
       at 1 6 (Bx1-0423 ∷ []) (refl) ▸ done


-- comm push SBOX(2;0;41;3) sw1 L: 7 steps
lem-comm-push-SBOX⟨2·0·41·3⟩-sw1-L : WsL → ⟪ (Sb2-0-41-3 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨2·0·41·3⟩-sw1-L c4 = run b0
  where
  b0 : Chain (Sb2-0-41-3 ∷ Sw12 ∷ []) (Sw12 ∷ Sb1-0-42-3 ∷ [])
  b0 = at 0 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 4 2 (Sw12 ∷ Sb⁻1-0-3-2 ∷ []) (lem-comm-push-SBOXd⟨2·0·3·1⟩-sw1-L c4) ▸
       at 3 2 (Sw12 ∷ Toff324 ∷ []) (sym (wl0038 c4)) ▸
       at 2 2 (Sw12 ∷ Sb1-0-3-2 ∷ []) (lem-comm-push-SBOX⟨2·0·3·1⟩-sw1-L c4) ▸
       at 1 2 (Sw12 ∷ Toff324 ∷ []) (sym (wl0038 c4)) ▸
       at 0 2 (Sw12 ∷ Bx1-0423 ∷ []) (lem-comm-push-BOX⟨2·0413⟩-sw1-L c4) ▸
       at 1 5 (Sb1-0-42-3 ∷ []) (refl) ▸ done


-- comm push SBOXd(1;0;3;2) sw0 L: 3 steps
lem-comm-push-SBOXd⟨1·0·3·2⟩-sw0-L : WsL → ⟪ (Sb⁻1-0-3-2 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Sb⁻0-1-3-2 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨1·0·3·2⟩-sw0-L c4 = run b0
  where
  b0 : Chain (Sb⁻1-0-3-2 ∷ Sw01 ∷ []) (Sw01 ∷ Sb⁻0-1-3-2 ∷ [])
  b0 = at 0 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 2 (Sw01 ∷ CS13⁻ ∷ []) (wl0042 c4) ▸
       at 1 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸ done


-- comm push SBOX(1;0;3;2) sw0 L: 3 steps
lem-comm-push-SBOX⟨1·0·3·2⟩-sw0-L : WsL → ⟪ (Sb1-0-3-2 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Sb0-1-3-2 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨1·0·3·2⟩-sw0-L c4 = run b0
  where
  b0 : Chain (Sb1-0-3-2 ∷ Sw01 ∷ []) (Sw01 ∷ Sb0-1-3-2 ∷ [])
  b0 = at 0 1 (CS03 ∷ []) (refl) ▸
       at 0 2 (Sw01 ∷ CS13 ∷ []) (wl0015 c4) ▸
       at 1 1 (Sb0-1-3-2 ∷ []) (refl) ▸ done


-- comm push BOX(1;03) sw0 L: 3 steps
lem-comm-push-BOX⟨1·03⟩-sw0-L : WsL → ⟪ (Bx1-03 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Bx0-13 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨1·03⟩-sw0-L c4 = run b0
  where
  b0 : Chain (Bx1-03 ∷ Sw01 ∷ []) (Sw01 ∷ Bx0-13 ∷ [])
  b0 = at 0 1 (CZ03 ∷ []) (refl) ▸
       at 0 2 (Sw01 ∷ CZ13 ∷ []) (wl0049 c4) ▸
       at 1 1 (Bx0-13 ∷ []) (refl) ▸ done


-- comm push BOX(0;123) sw0 L: 8 steps
lem-comm-push-BOX⟨0·123⟩-sw0-L : WsL → ⟪ (Bx0-123 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Bx1-023 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·123⟩-sw0-L c4 = run b0
  where
  b0 : Chain (Bx0-123 ∷ Sw01 ∷ []) (Sw01 ∷ Bx1-023 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ Toff012 ∷ Bx1-03 ∷ Toff012 ∷ CCZ012 ∷ Bx1-03 ∷ []) (refl) ▸
       at 5 2 (Sw01 ∷ Bx0-13 ∷ []) (lem-comm-push-BOX⟨1·03⟩-sw0-L c4) ▸
       at 4 2 (Sw01 ∷ CCZ012 ∷ []) (wl0103 c4) ▸
       at 3 2 (Sw01 ∷ Toff102 ∷ []) (sym (wl0104 c4)) ▸
       at 2 2 (Sw01 ∷ Bx0-13 ∷ []) (lem-comm-push-BOX⟨1·03⟩-sw0-L c4) ▸
       at 1 2 (Sw01 ∷ Toff102 ∷ []) (sym (wl0104 c4)) ▸
       at 0 2 (Sw01 ∷ CCZ012 ∷ []) (wl0103 c4) ▸
       at 1 6 (Bx1-023 ∷ []) (refl) ▸ done


-- comm push CSd14 sw0 L: 5 steps
lem-comm-push-CSd14-sw0-L : WsL → ⟪ (CS14⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CS04⁻ ∷ []) ⟫ʷ
lem-comm-push-CSd14-sw0-L c4 = run b0
  where
  b0 : Chain (CS14⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS04⁻ ∷ [])
  b0 = at 0 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 1 2 (Sw01 ∷ CS03⁻ ∷ []) (wl0105 c4) ▸
       at 0 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 1 3 (CS04⁻ ∷ []) (by-assoc Eq.refl) ▸ done


-- comm push CS14 sw0 L: 5 steps
lem-comm-push-CS14-sw0-L : WsL → ⟪ (CS14 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CS04 ∷ []) ⟫ʷ
lem-comm-push-CS14-sw0-L c4 = run b0
  where
  b0 : Chain (CS14 ∷ Sw01 ∷ []) (Sw01 ∷ CS04 ∷ [])
  b0 = at 0 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 1 2 (Sw01 ∷ CS03 ∷ []) (wl0106 c4) ▸
       at 0 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 1 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm push CCZ014 sw0 L: 48 steps
lem-comm-push-CCZ014-sw0-L : WsL → ⟪ (CCZ014 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CCZ014 ∷ []) ⟫ʷ
lem-comm-push-CCZ014-sw0-L c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (run b5)))))
  where
  b0 : Chain (CCZ014 ∷ Sw01 ∷ []) (Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw34 ∷ Sw01 ∷ [])
  b0 = at 0 1 (Sw34 ∷ CCZ013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 3 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw34 ∷ Sw01 ∷ []) (CS14 ∷ CX01 ∷ Sw34 ∷ CS13⁻ ∷ Sw34 ∷ Sw34 ∷ CX01 ∷ CS03 ∷ Sw34 ∷ Sw01 ∷ [])
  b1 = at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0003 c4) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 0 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 4 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸ done

  b2 : Chain (CS14 ∷ CX01 ∷ Sw34 ∷ CS13⁻ ∷ Sw34 ∷ Sw34 ∷ CX01 ∷ CS03 ∷ Sw34 ∷ Sw01 ∷ []) (CS14 ∷ CX01 ∷ Sw01 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ [])
  b2 = at 2 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 4 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0004 c4) ▸
       at 4 2 (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L c4) ▸
       at 3 2 (Sw01 ∷ CX10 ∷ []) (wl0107 c4) ▸
       at 2 2 (Sw01 ∷ CS04⁻ ∷ []) (lem-comm-push-CSd14-sw0-L c4) ▸ done

  b3 : Chain (CS14 ∷ CX01 ∷ Sw01 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ []) (Sw01 ∷ Sw34 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ Sw34 ∷ CX10 ∷ CS14 ∷ [])
  b3 = at 1 2 (Sw01 ∷ CX10 ∷ []) (wl0107 c4) ▸
       at 0 2 (Sw01 ∷ CS04 ∷ []) (lem-comm-push-CS14-sw0-L c4) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0004 c4) ▸
       at 3 2 (CX10 ∷ Sw34 ∷ []) (sym (c₂ (CX₁₀) (Swap ↑))) ▸
       at 5 1 (Sw34 ∷ CS03⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0004 c4) ▸ done

  b4 : Chain (Sw01 ∷ Sw34 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ Sw34 ∷ CX10 ∷ CS14 ∷ []) (Sw01 ∷ Sw34 ∷ Sw23 ∷ CS02 ∷ CX10 ∷ Sw23 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ CX10 ∷ CS13 ∷ Sw34 ∷ [])
  b4 = at 5 2 (CX10 ∷ Sw34 ∷ []) (sym (c₂ (CX₁₀) (Swap ↑))) ▸
       at 7 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0004 c4) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0003 c4) ▸
       at 4 2 (CX10 ∷ Sw23 ∷ []) (sym (c₂ (CX₁₀) (Swap))) ▸
       at 6 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b5 : Chain (Sw01 ∷ Sw34 ∷ Sw23 ∷ CS02 ∷ CX10 ∷ Sw23 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ CX10 ∷ CS13 ∷ Sw34 ∷ []) (Sw01 ∷ CCZ014 ∷ [])
  b5 = at 5 2 [] (wl0003 c4) ▸
       at 6 2 (CX10 ∷ Sw23 ∷ []) (sym (c₂ (CX₁₀) (Swap))) ▸
       at 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0003 c4) ▸
       at 3 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wl0108 c4) ▸
       at 3 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (CCZ014 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm push TOFF104 sw0 L: 63 steps
lem-comm-push-TOFF104-sw0-L : WsL → ⟪ (Toff104 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Toff014 ∷ []) ⟫ʷ
lem-comm-push-TOFF104-sw0-L c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (Toff104 ∷ Sw01 ∷ []) (Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw01 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Toff103 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸ done

  b1 : Chain (Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw01 ∷ []) (K1 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw01 ∷ [])
  b1 = at 4 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 9 2 [] (wl0003 c4) ▸
       at 0 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸ done

  b2 : Chain (K1 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw01 ∷ []) (K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw34 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw01 ∷ [])
  b2 = at 3 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 5 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw34 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw01 ∷ []) (K1 ∷ CS14 ∷ CX01 ∷ Sw01 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ K0 ∷ ι ∷ [])
  b3 = at 6 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 7 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 8 2 [] (wl0004 c4) ▸
       at 7 2 (Sw01 ∷ ι ∷ []) (sym (wl0025 c4)) ▸
       at 6 2 (Sw01 ∷ K0 ∷ []) (wl0109 c4) ▸
       at 5 2 (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L c4) ▸
       at 4 2 (Sw01 ∷ CX10 ∷ []) (wl0107 c4) ▸
       at 3 2 (Sw01 ∷ CS04⁻ ∷ []) (lem-comm-push-CSd14-sw0-L c4) ▸ done

  b4 : Chain (K1 ∷ CS14 ∷ CX01 ∷ Sw01 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ K0 ∷ ι ∷ []) (Sw01 ∷ Sw34 ∷ K0 ∷ CS03 ∷ CX10 ∷ Sw34 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ K0 ∷ ι ∷ [])
  b4 = at 2 2 (Sw01 ∷ CX10 ∷ []) (wl0107 c4) ▸
       at 1 2 (Sw01 ∷ CS04 ∷ []) (lem-comm-push-CS14-sw0-L c4) ▸
       at 0 2 (Sw01 ∷ K0 ∷ []) (wl0109 c4) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 4 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0004 c4) ▸
       at 4 2 (CX10 ∷ Sw34 ∷ []) (sym (c₂ (CX₁₀) (Swap ↑))) ▸ done

  b5 : Chain (Sw01 ∷ Sw34 ∷ K0 ∷ CS03 ∷ CX10 ∷ Sw34 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ K0 ∷ ι ∷ []) (Sw01 ∷ Sw34 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K0 ∷ ι ∷ Sw34 ∷ [])
  b5 = at 6 1 (Sw34 ∷ CS03⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0004 c4) ▸
       at 6 2 (CX10 ∷ Sw34 ∷ []) (sym (c₂ (CX₁₀) (Swap ↑))) ▸
       at 8 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0004 c4) ▸
       at 8 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 9 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸ done

  b6 : Chain (Sw01 ∷ Sw34 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K0 ∷ ι ∷ Sw34 ∷ []) (Sw01 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw34 ∷ [])
  b6 = at 3 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0003 c4) ▸
       at 5 2 (CX10 ∷ Sw23 ∷ []) (sym (c₂ (CX₁₀) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0003 c4) ▸
       at 7 2 (CX10 ∷ Sw23 ∷ []) (sym (c₂ (CX₁₀) (Swap))) ▸
       at 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b7 : Chain (Sw01 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw34 ∷ []) (Sw01 ∷ Toff014 ∷ [])
  b7 = at 8 2 [] (wl0003 c4) ▸
       at 9 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 10 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 3 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (wl0110 c4) ▸
       at 3 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff014 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm push BOX(1;0423) sw0 L: 8 steps
lem-comm-push-BOX⟨1·0423⟩-sw0-L : WsL → ⟪ (Bx1-0423 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨1·0423⟩-sw0-L c4 = run b0
  where
  b0 : Chain (Bx1-0423 ∷ Sw01 ∷ []) (Sw01 ∷ Bx0-1423 ∷ [])
  b0 = at 0 1 (CCZ014 ∷ Toff104 ∷ Bx0-123 ∷ Toff104 ∷ CCZ014 ∷ Bx0-123 ∷ []) (refl) ▸
       at 5 2 (Sw01 ∷ Bx1-023 ∷ []) (lem-comm-push-BOX⟨0·123⟩-sw0-L c4) ▸
       at 4 2 (Sw01 ∷ CCZ014 ∷ []) (lem-comm-push-CCZ014-sw0-L c4) ▸
       at 3 2 (Sw01 ∷ Toff014 ∷ []) (lem-comm-push-TOFF104-sw0-L c4) ▸
       at 2 2 (Sw01 ∷ Bx1-023 ∷ []) (lem-comm-push-BOX⟨0·123⟩-sw0-L c4) ▸
       at 1 2 (Sw01 ∷ Toff014 ∷ []) (lem-comm-push-TOFF104-sw0-L c4) ▸
       at 0 2 (Sw01 ∷ CCZ014 ∷ []) (lem-comm-push-CCZ014-sw0-L c4) ▸
       at 1 6 (Bx0-1423 ∷ []) (refl) ▸ done


-- comm push SBOX(1;0;42;3) sw0 L: 7 steps
lem-comm-push-SBOX⟨1·0·42·3⟩-sw0-L : WsL → ⟪ (Sb1-0-42-3 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨1·0·42·3⟩-sw0-L c4 = run b0
  where
  b0 : Chain (Sb1-0-42-3 ∷ Sw01 ∷ []) (Sw01 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (refl) ▸
       at 4 2 (Sw01 ∷ Sb⁻0-1-3-2 ∷ []) (lem-comm-push-SBOXd⟨1·0·3·2⟩-sw0-L c4) ▸
       at 3 2 (Sw01 ∷ Toff324 ∷ []) (sym (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI))) ▸
       at 2 2 (Sw01 ∷ Sb0-1-3-2 ∷ []) (lem-comm-push-SBOX⟨1·0·3·2⟩-sw0-L c4) ▸
       at 1 2 (Sw01 ∷ Toff324 ∷ []) (sym (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI))) ▸
       at 0 2 (Sw01 ∷ Bx0-1423 ∷ []) (lem-comm-push-BOX⟨1·0423⟩-sw0-L c4) ▸
       at 1 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done


-- comm push SBOXd(0;1;3;2) sw2 L: 4 steps
lem-comm-push-SBOXd⟨0·1·3·2⟩-sw2-L : WsL → ⟪ (Sb⁻0-1-3-2 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sb⁻0-1-2-3 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨0·1·3·2⟩-sw2-L c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-3-2 ∷ Sw23 ∷ []) (Sw23 ∷ Sb⁻0-1-2-3 ∷ [])
  b0 = at 0 1 (CS13⁻ ∷ []) (refl) ▸
       at 0 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0003 c4) ▸
       at 1 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸ done


-- comm push SBOX(0;1;3;2) sw2 L: 4 steps
lem-comm-push-SBOX⟨0·1·3·2⟩-sw2-L : WsL → ⟪ (Sb0-1-3-2 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sb0-1-2-3 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨0·1·3·2⟩-sw2-L c4 = run b0
  where
  b0 : Chain (Sb0-1-3-2 ∷ Sw23 ∷ []) (Sw23 ∷ Sb0-1-2-3 ∷ [])
  b0 = at 0 1 (CS13 ∷ []) (refl) ▸
       at 0 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0003 c4) ▸
       at 1 1 (Sb0-1-2-3 ∷ []) (refl) ▸ done


-- comm push BOX(0;13) sw2 L: 4 steps
lem-comm-push-BOX⟨0·13⟩-sw2-L : WsL → ⟪ (Bx0-13 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Bx0-12 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·13⟩-sw2-L c4 = run b0
  where
  b0 : Chain (Bx0-13 ∷ Sw23 ∷ []) (Sw23 ∷ Bx0-12 ∷ [])
  b0 = at 0 1 (CZ13 ∷ []) (refl) ▸
       at 0 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0003 c4) ▸
       at 1 1 (Bx0-12 ∷ []) (refl) ▸ done


-- comm push BOX(1;023) sw2 L: 12 steps
lem-comm-push-BOX⟨1·023⟩-sw2-L : WsL → ⟪ (Bx1-023 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Bx1-032 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨1·023⟩-sw2-L c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx1-023 ∷ Sw23 ∷ []) (CCZ012 ∷ Sw23 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Bx0-12 ∷ Toff103 ∷ CCZ013 ∷ Bx0-12 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ []) (refl) ▸
       at 5 2 (Sw23 ∷ Bx0-12 ∷ []) (lem-comm-push-BOX⟨0·13⟩-sw2-L c4) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 5 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (Toff103 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw23 ∷ Bx0-12 ∷ []) (lem-comm-push-BOX⟨0·13⟩-sw2-L c4) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸ done

  b1 : Chain (CCZ012 ∷ Sw23 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Bx0-12 ∷ Toff103 ∷ CCZ013 ∷ Bx0-12 ∷ []) (Sw23 ∷ Bx1-032 ∷ [])
  b1 = at 2 3 (Toff103 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 1 6 (Bx1-032 ∷ []) (refl) ▸ done


-- comm push BOX(0;1423) sw2 L: 8 steps
lem-comm-push-BOX⟨0·1423⟩-sw2-L : WsL → ⟪ (Bx0-1423 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Bx0-1432 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·1423⟩-sw2-L c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ Sw23 ∷ []) (Sw23 ∷ Bx0-1432 ∷ [])
  b0 = at 0 1 (CCZ014 ∷ Toff014 ∷ Bx1-023 ∷ Toff014 ∷ CCZ014 ∷ Bx1-023 ∷ []) (refl) ▸
       at 5 2 (Sw23 ∷ Bx1-032 ∷ []) (lem-comm-push-BOX⟨1·023⟩-sw2-L c4) ▸
       at 4 2 (Sw23 ∷ CCZ014 ∷ []) (lem-comm-push-CCZ014-sw2-L c4) ▸
       at 3 2 (Sw23 ∷ Toff014 ∷ []) (lem-comm-push-TOFF014-sw2-L c4) ▸
       at 2 2 (Sw23 ∷ Bx1-032 ∷ []) (lem-comm-push-BOX⟨1·023⟩-sw2-L c4) ▸
       at 1 2 (Sw23 ∷ Toff014 ∷ []) (lem-comm-push-TOFF014-sw2-L c4) ▸
       at 0 2 (Sw23 ∷ CCZ014 ∷ []) (lem-comm-push-CCZ014-sw2-L c4) ▸
       at 1 6 (Bx0-1432 ∷ []) (refl) ▸ done


-- comm push SBOX(0;1;42;3) sw2 L: 7 steps
lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L : WsL → ⟪ (Sb0-1-42-3 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ Sw23 ∷ []) (Sw23 ∷ Sb0-1-43-2 ∷ [])
  b0 = at 0 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 4 2 (Sw23 ∷ Sb⁻0-1-2-3 ∷ []) (lem-comm-push-SBOXd⟨0·1·3·2⟩-sw2-L c4) ▸
       at 3 2 (Sw23 ∷ Toff234 ∷ []) (sym (wl0111 c4)) ▸
       at 2 2 (Sw23 ∷ Sb0-1-2-3 ∷ []) (lem-comm-push-SBOX⟨0·1·3·2⟩-sw2-L c4) ▸
       at 1 2 (Sw23 ∷ Toff234 ∷ []) (sym (wl0111 c4)) ▸
       at 0 2 (Sw23 ∷ Bx0-1432 ∷ []) (lem-comm-push-BOX⟨0·1423⟩-sw2-L c4) ▸
       at 1 5 (Sb0-1-43-2 ∷ []) (refl) ▸ done


-- comm push SBOXd(0;1;2;3) sw1 L: 3 steps
lem-comm-push-SBOXd⟨0·1·2·3⟩-sw1-L : WsL → ⟪ (Sb⁻0-1-2-3 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sb⁻0-2-1-3 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨0·1·2·3⟩-sw1-L c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-2-3 ∷ Sw12 ∷ []) (Sw12 ∷ Sb⁻0-2-1-3 ∷ [])
  b0 = at 0 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 2 (Sw12 ∷ CS12⁻ ∷ []) (wl0112 c4) ▸
       at 1 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸ done


-- comm push SBOX(0;1;2;3) sw1 L: 3 steps
lem-comm-push-SBOX⟨0·1·2·3⟩-sw1-L : WsL → ⟪ (Sb0-1-2-3 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sb0-2-1-3 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨0·1·2·3⟩-sw1-L c4 = run b0
  where
  b0 : Chain (Sb0-1-2-3 ∷ Sw12 ∷ []) (Sw12 ∷ Sb0-2-1-3 ∷ [])
  b0 = at 0 1 (CS12 ∷ []) (refl) ▸
       at 0 2 (Sw12 ∷ CS12 ∷ []) (wl0113 c4) ▸
       at 1 1 (Sb0-2-1-3 ∷ []) (refl) ▸ done


-- comm push BOX(0;12) sw1 L: 3 steps
lem-comm-push-BOX⟨0·12⟩-sw1-L : WsL → ⟪ (Bx0-12 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Bx0-21 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·12⟩-sw1-L c4 = run b0
  where
  b0 : Chain (Bx0-12 ∷ Sw12 ∷ []) (Sw12 ∷ Bx0-21 ∷ [])
  b0 = at 0 1 (CZ12 ∷ []) (refl) ▸
       at 0 2 (Sw12 ∷ CZ12 ∷ []) (wl0114 c4) ▸
       at 1 1 (Bx0-21 ∷ []) (refl) ▸ done


-- comm push BOX(1;032) sw1 L: 12 steps
lem-comm-push-BOX⟨1·032⟩-sw1-L : WsL → ⟪ (Bx1-032 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Bx2-031 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨1·032⟩-sw1-L c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx1-032 ∷ Sw12 ∷ []) (CCZ013 ∷ Sw12 ∷ Sw12 ∷ Toff103 ∷ Sw12 ∷ Bx0-21 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ [])
  b0 = at 0 1 (CCZ013 ∷ Toff103 ∷ Bx0-12 ∷ Toff103 ∷ CCZ013 ∷ Bx0-12 ∷ []) (refl) ▸
       at 5 2 (Sw12 ∷ Bx0-21 ∷ []) (lem-comm-push-BOX⟨0·12⟩-sw1-L c4) ▸
       at 4 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 5 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 4 3 (Toff203 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw12 ∷ Bx0-21 ∷ []) (lem-comm-push-BOX⟨0·12⟩-sw1-L c4) ▸
       at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸ done

  b1 : Chain (CCZ013 ∷ Sw12 ∷ Sw12 ∷ Toff103 ∷ Sw12 ∷ Bx0-21 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ []) (Sw12 ∷ Bx2-031 ∷ [])
  b1 = at 2 3 (Toff203 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 1 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸
       at 1 6 (Bx2-031 ∷ []) (refl) ▸ done


-- comm push BOX(0;1432) sw1 L: 12 steps
lem-comm-push-BOX⟨0·1432⟩-sw1-L : WsL → ⟪ (Bx0-1432 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Bx0-2431 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·1432⟩-sw1-L c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-1432 ∷ Sw12 ∷ []) (CCZ014 ∷ Sw12 ∷ Sw12 ∷ Toff014 ∷ Sw12 ∷ Bx2-031 ∷ Toff024 ∷ CCZ024 ∷ Bx2-031 ∷ [])
  b0 = at 0 1 (CCZ014 ∷ Toff014 ∷ Bx1-032 ∷ Toff014 ∷ CCZ014 ∷ Bx1-032 ∷ []) (refl) ▸
       at 5 2 (Sw12 ∷ Bx2-031 ∷ []) (lem-comm-push-BOX⟨1·032⟩-sw1-L c4) ▸
       at 4 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 5 3 (CCZ024 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 4 3 (Toff024 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw12 ∷ Bx2-031 ∷ []) (lem-comm-push-BOX⟨1·032⟩-sw1-L c4) ▸
       at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸ done

  b1 : Chain (CCZ014 ∷ Sw12 ∷ Sw12 ∷ Toff014 ∷ Sw12 ∷ Bx2-031 ∷ Toff024 ∷ CCZ024 ∷ Bx2-031 ∷ []) (Sw12 ∷ Bx0-2431 ∷ [])
  b1 = at 2 3 (Toff024 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 1 3 (CCZ024 ∷ []) (by-assoc Eq.refl) ▸
       at 1 6 (Bx0-2431 ∷ []) (refl) ▸ done


-- comm push SBOX(0;1;43;2) sw1 L: 7 steps
lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L : WsL → ⟪ (Sb0-1-43-2 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L c4 = run b0
  where
  b0 : Chain (Sb0-1-43-2 ∷ Sw12 ∷ []) (Sw12 ∷ Sb0-2-43-1 ∷ [])
  b0 = at 0 1 (Bx0-1432 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 4 2 (Sw12 ∷ Sb⁻0-2-1-3 ∷ []) (lem-comm-push-SBOXd⟨0·1·2·3⟩-sw1-L c4) ▸
       at 3 2 (Sw12 ∷ Toff134 ∷ []) (sym (wl0083 c4)) ▸
       at 2 2 (Sw12 ∷ Sb0-2-1-3 ∷ []) (lem-comm-push-SBOX⟨0·1·2·3⟩-sw1-L c4) ▸
       at 1 2 (Sw12 ∷ Toff134 ∷ []) (sym (wl0083 c4)) ▸
       at 0 2 (Sw12 ∷ Bx0-2431 ∷ []) (lem-comm-push-BOX⟨0·1432⟩-sw1-L c4) ▸
       at 1 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done


-- comm push BOX(0;21) sw1 R: 3 steps
lem-comm-push-BOX⟨0·21⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Bx0-21 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-12 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·21⟩-sw1-R c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-21 ∷ []) (Bx0-12 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ12 ∷ []) (refl) ▸
       at 0 2 (CZ12 ∷ Sw12 ∷ []) (sym (wl0114 c4)) ▸
       at 0 1 (Bx0-12 ∷ []) (refl) ▸ done


-- comm push BOX(2;031) sw1 R: 12 steps
lem-comm-push-BOX⟨2·031⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Bx2-031 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-032 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨2·031⟩-sw1-R c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw12 ∷ Bx2-031 ∷ []) (CCZ013 ∷ Toff103 ∷ Bx0-12 ∷ Toff103 ∷ Sw12 ∷ CCZ023 ∷ Bx0-21 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ []) (refl) ▸
       at 1 1 (Sw12 ∷ CCZ013 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0006 c4) ▸
       at 2 1 (Sw12 ∷ Toff103 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0006 c4) ▸
       at 2 2 (Bx0-12 ∷ Sw12 ∷ []) (lem-comm-push-BOX⟨0·21⟩-sw1-R c4) ▸
       at 4 1 (Sw12 ∷ Toff103 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0006 c4) ▸ done

  b1 : Chain (CCZ013 ∷ Toff103 ∷ Bx0-12 ∷ Toff103 ∷ Sw12 ∷ CCZ023 ∷ Bx0-21 ∷ []) (Bx1-032 ∷ Sw12 ∷ [])
  b1 = at 5 1 (Sw12 ∷ CCZ013 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0006 c4) ▸
       at 5 2 (Bx0-12 ∷ Sw12 ∷ []) (lem-comm-push-BOX⟨0·21⟩-sw1-R c4) ▸
       at 0 6 (Bx1-032 ∷ []) (refl) ▸ done


-- comm push BOX(0;2431) sw1 R: 12 steps
lem-comm-push-BOX⟨0·2431⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·2431⟩-sw1-R c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw12 ∷ Bx0-2431 ∷ []) (CCZ014 ∷ Toff014 ∷ Bx1-032 ∷ Toff014 ∷ Sw12 ∷ CCZ024 ∷ Bx2-031 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx2-031 ∷ Toff024 ∷ CCZ024 ∷ Bx2-031 ∷ []) (refl) ▸
       at 1 1 (Sw12 ∷ CCZ014 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0006 c4) ▸
       at 2 1 (Sw12 ∷ Toff014 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0006 c4) ▸
       at 2 2 (Bx1-032 ∷ Sw12 ∷ []) (lem-comm-push-BOX⟨2·031⟩-sw1-R c4) ▸
       at 4 1 (Sw12 ∷ Toff014 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0006 c4) ▸ done

  b1 : Chain (CCZ014 ∷ Toff014 ∷ Bx1-032 ∷ Toff014 ∷ Sw12 ∷ CCZ024 ∷ Bx2-031 ∷ []) (Bx0-1432 ∷ Sw12 ∷ [])
  b1 = at 5 1 (Sw12 ∷ CCZ014 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0006 c4) ▸
       at 5 2 (Bx1-032 ∷ Sw12 ∷ []) (lem-comm-push-BOX⟨2·031⟩-sw1-R c4) ▸
       at 0 6 (Bx0-1432 ∷ []) (refl) ▸ done


-- comm push SBOX(0;2;1;3) sw1 R: 3 steps
lem-comm-push-SBOX⟨0·2·1·3⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Sb0-2-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-2-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨0·2·1·3⟩-sw1-R c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb0-2-1-3 ∷ []) (Sb0-1-2-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS12 ∷ []) (refl) ▸
       at 0 2 (CS12 ∷ Sw12 ∷ []) (sym (wl0113 c4)) ▸
       at 0 1 (Sb0-1-2-3 ∷ []) (refl) ▸ done


-- comm push SBOXd(0;2;1;3) sw1 R: 3 steps
lem-comm-push-SBOXd⟨0·2·1·3⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Sb⁻0-2-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-2-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨0·2·1·3⟩-sw1-R c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻0-2-1-3 ∷ []) (Sb⁻0-1-2-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 2 (CS12⁻ ∷ Sw12 ∷ []) (sym (wl0112 c4)) ▸
       at 0 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸ done


-- comm push SBOX(0;2;43;1) sw1 R: 7 steps
lem-comm-push-SBOX⟨0·2·43·1⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-43-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨0·2·43·1⟩-sw1-R c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb0-2-43-1 ∷ []) (Sb0-1-43-2 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 0 2 (Bx0-1432 ∷ Sw12 ∷ []) (lem-comm-push-BOX⟨0·2431⟩-sw1-R c4) ▸
       at 1 2 (Toff234 ∷ Sw12 ∷ []) (wl0083 c4) ▸
       at 2 2 (Sb0-1-2-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·2·1·3⟩-sw1-R c4) ▸
       at 3 2 (Toff234 ∷ Sw12 ∷ []) (wl0083 c4) ▸
       at 4 2 (Sb⁻0-1-2-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOXd⟨0·2·1·3⟩-sw1-R c4) ▸
       at 0 5 (Sb0-1-43-2 ∷ []) (refl) ▸ done


-- comm push CCZ014 sw2 R: 47 steps
lem-comm-push-CCZ014-sw2-R : WsL → ⟪ (Sw23 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-CCZ014-sw2-R c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (run b5)))))
  where
  b0 : Chain (Sw23 ∷ CCZ014 ∷ []) (Sw23 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CCZ013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ CS14 ∷ CX01 ∷ Sw34 ∷ CS13⁻ ∷ Sw34 ∷ Sw34 ∷ CX01 ∷ CS03 ∷ Sw34 ∷ [])
  b1 = at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0003 c4) ▸
       at 3 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸ done

  b2 : Chain (Sw23 ∷ CS14 ∷ CX01 ∷ Sw34 ∷ CS13⁻ ∷ Sw34 ∷ Sw34 ∷ CX01 ∷ CS03 ∷ Sw34 ∷ []) (CS14 ∷ CX01 ∷ CS14⁻ ∷ Sw23 ∷ CX01 ∷ CS04 ∷ [])
  b2 = at 3 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 5 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0004 c4) ▸
       at 0 2 (CS14 ∷ Sw23 ∷ []) (sym (wl0017 c4)) ▸
       at 1 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 2 2 (CS14⁻ ∷ Sw23 ∷ []) (sym (wl0048 c4)) ▸ done

  b3 : Chain (CS14 ∷ CX01 ∷ CS14⁻ ∷ Sw23 ∷ CX01 ∷ CS04 ∷ []) (Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw34 ∷ CX01 ∷ CS04 ∷ Sw23 ∷ [])
  b3 = at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 4 2 (CS04 ∷ Sw23 ∷ []) (lem-comm-push-CS04-sw2-R c4) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0004 c4) ▸
       at 2 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 4 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0004 c4) ▸ done

  b4 : Chain (Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw34 ∷ CX01 ∷ CS04 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ Sw23 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ Sw34 ∷ Sw23 ∷ [])
  b4 = at 4 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0004 c4) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0003 c4) ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b5 : Chain (Sw34 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ Sw23 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ Sw34 ∷ Sw23 ∷ []) (CCZ014 ∷ Sw23 ∷ [])
  b5 = at 4 2 [] (wl0003 c4) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0003 c4) ▸
       at 2 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (CCZ014 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm push TOFF014 sw2 R: 62 steps
lem-comm-push-TOFF014-sw2-R : WsL → ⟪ (Sw23 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-TOFF014-sw2-R c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (Sw23 ∷ Toff014 ∷ []) (Sw23 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸ done

  b1 : Chain (Sw23 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ K0 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ [])
  b1 = at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 10 2 [] (wl0003 c4) ▸
       at 1 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸ done

  b2 : Chain (Sw23 ∷ K0 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ []) (Sw23 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw34 ∷ [])
  b2 = at 4 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 4 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (Sw23 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw34 ∷ []) (K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw23 ∷ CS04 ∷ K0 ∷ ι ∷ [])
  b3 = at 7 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 8 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 9 2 [] (wl0004 c4) ▸
       at 0 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 1 2 (CS14 ∷ Sw23 ∷ []) (sym (wl0017 c4)) ▸
       at 2 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 3 2 (CS14⁻ ∷ Sw23 ∷ []) (sym (wl0048 c4)) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸ done

  b4 : Chain (K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw23 ∷ CS04 ∷ K0 ∷ ι ∷ []) (Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw34 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw23 ∷ [])
  b4 = at 5 2 (CS04 ∷ Sw23 ∷ []) (lem-comm-push-CS04-sw2-R c4) ▸
       at 6 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 7 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 3 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0004 c4) ▸
       at 3 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸ done

  b5 : Chain (Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw34 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw23 ∷ [])
  b5 = at 5 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0004 c4) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0004 c4) ▸
       at 7 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 8 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸ done

  b6 : Chain (Sw34 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw23 ∷ [])
  b6 = at 2 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0003 c4) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0003 c4) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b7 : Chain (Sw34 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw23 ∷ []) (Toff014 ∷ Sw23 ∷ [])
  b7 = at 7 2 [] (wl0003 c4) ▸
       at 8 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 2 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff014 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm push BOX(0;12) sw2 R: 4 steps
lem-comm-push-BOX⟨0·12⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Bx0-12 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-13 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·12⟩-sw2-R c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-12 ∷ []) (Bx0-13 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ12 ∷ []) (refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 0 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸
       at 0 1 (Bx0-13 ∷ []) (refl) ▸ done


-- comm push BOX(1;032) sw2 R: 12 steps
lem-comm-push-BOX⟨1·032⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Bx1-032 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-023 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨1·032⟩-sw2-R c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw23 ∷ Bx1-032 ∷ []) (CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ Sw23 ∷ CCZ013 ∷ Bx0-12 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff103 ∷ Bx0-12 ∷ Toff103 ∷ CCZ013 ∷ Bx0-12 ∷ []) (refl) ▸
       at 1 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0003 c4) ▸
       at 2 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0003 c4) ▸
       at 2 2 (Bx0-13 ∷ Sw23 ∷ []) (lem-comm-push-BOX⟨0·12⟩-sw2-R c4) ▸
       at 4 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0003 c4) ▸ done

  b1 : Chain (CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ Sw23 ∷ CCZ013 ∷ Bx0-12 ∷ []) (Bx1-023 ∷ Sw23 ∷ [])
  b1 = at 5 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0003 c4) ▸
       at 5 2 (Bx0-13 ∷ Sw23 ∷ []) (lem-comm-push-BOX⟨0·12⟩-sw2-R c4) ▸
       at 0 6 (Bx1-023 ∷ []) (refl) ▸ done


-- comm push BOX(0;1432) sw2 R: 8 steps
lem-comm-push-BOX⟨0·1432⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Bx0-1432 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·1432⟩-sw2-R c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-1432 ∷ []) (Bx0-1423 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff014 ∷ Bx1-032 ∷ Toff014 ∷ CCZ014 ∷ Bx1-032 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw23 ∷ []) (lem-comm-push-CCZ014-sw2-R c4) ▸
       at 1 2 (Toff014 ∷ Sw23 ∷ []) (lem-comm-push-TOFF014-sw2-R c4) ▸
       at 2 2 (Bx1-023 ∷ Sw23 ∷ []) (lem-comm-push-BOX⟨1·032⟩-sw2-R c4) ▸
       at 3 2 (Toff014 ∷ Sw23 ∷ []) (lem-comm-push-TOFF014-sw2-R c4) ▸
       at 4 2 (CCZ014 ∷ Sw23 ∷ []) (lem-comm-push-CCZ014-sw2-R c4) ▸
       at 5 2 (Bx1-023 ∷ Sw23 ∷ []) (lem-comm-push-BOX⟨1·032⟩-sw2-R c4) ▸
       at 0 6 (Bx0-1423 ∷ []) (refl) ▸ done


-- comm push SBOX(0;1;2;3) sw2 R: 4 steps
lem-comm-push-SBOX⟨0·1·2·3⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Sb0-1-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-3-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨0·1·2·3⟩-sw2-R c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb0-1-2-3 ∷ []) (Sb0-1-3-2 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS12 ∷ []) (refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 0 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 0 1 (Sb0-1-3-2 ∷ []) (refl) ▸ done


-- comm push SBOXd(0;1;2;3) sw2 R: 4 steps
lem-comm-push-SBOXd⟨0·1·2·3⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Sb⁻0-1-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-3-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨0·1·2·3⟩-sw2-R c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻0-1-2-3 ∷ []) (Sb⁻0-1-3-2 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS12⁻ ∷ []) (refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 0 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 0 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸ done


-- comm push SBOX(0;1;43;2) sw2 R: 7 steps
lem-comm-push-SBOX⟨0·1·43·2⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨0·1·43·2⟩-sw2-R c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb0-1-43-2 ∷ []) (Sb0-1-42-3 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx0-1432 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 0 2 (Bx0-1423 ∷ Sw23 ∷ []) (lem-comm-push-BOX⟨0·1432⟩-sw2-R c4) ▸
       at 1 2 (Toff324 ∷ Sw23 ∷ []) (wl0111 c4) ▸
       at 2 2 (Sb0-1-3-2 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·1·2·3⟩-sw2-R c4) ▸
       at 3 2 (Toff324 ∷ Sw23 ∷ []) (wl0111 c4) ▸
       at 4 2 (Sb⁻0-1-3-2 ∷ Sw23 ∷ []) (lem-comm-push-SBOXd⟨0·1·2·3⟩-sw2-R c4) ▸
       at 0 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done


-- comm push CK41 sw0 R: 5 steps
lem-comm-push-CK41-sw0-R : WsL → ⟪ (Sw01 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-CK41-sw0-R c4 = run b0
  where
  b0 : Chain (Sw01 ∷ CK41 ∷ []) (CK40 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CK31 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 1 2 (CK30 ∷ Sw01 ∷ []) (sym (wl0081 c4)) ▸
       at 2 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 0 3 (CK40 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm push CS14 sw0 R: 5 steps
lem-comm-push-CS14-sw0-R : WsL → ⟪ (Sw01 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-CS14-sw0-R c4 = run b0
  where
  b0 : Chain (Sw01 ∷ CS14 ∷ []) (CS04 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 1 2 (CS03 ∷ Sw01 ∷ []) (sym (wl0015 c4)) ▸
       at 2 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 0 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm push CSd14 sw0 R: 5 steps
lem-comm-push-CSd14-sw0-R : WsL → ⟪ (Sw01 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS04⁻ ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-CSd14-sw0-R c4 = run b0
  where
  b0 : Chain (Sw01 ∷ CS14⁻ ∷ []) (CS04⁻ ∷ Sw01 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 1 2 (CS03⁻ ∷ Sw01 ∷ []) (sym (wl0042 c4)) ▸
       at 2 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 0 3 (CS04⁻ ∷ []) (by-assoc Eq.refl) ▸ done


-- comm push CS04 sw0 R: 5 steps
lem-comm-push-CS04-sw0-R : WsL → ⟪ (Sw01 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-CS04-sw0-R c4 = run b0
  where
  b0 : Chain (Sw01 ∷ CS04 ∷ []) (CS14 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 1 2 (CS13 ∷ Sw01 ∷ []) (sym (wl0106 c4)) ▸
       at 2 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 0 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm push CCZ014 sw0 R: 48 steps
lem-comm-push-CCZ014-sw0-R : WsL → ⟪ (Sw01 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-CCZ014-sw0-R c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (run b5)))))
  where
  b0 : Chain (Sw01 ∷ CCZ014 ∷ []) (Sw01 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CCZ013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw01 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw34 ∷ []) (Sw01 ∷ CS14 ∷ CX01 ∷ Sw34 ∷ CS13⁻ ∷ Sw34 ∷ Sw34 ∷ CX01 ∷ CS03 ∷ Sw34 ∷ [])
  b1 = at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0003 c4) ▸
       at 3 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸ done

  b2 : Chain (Sw01 ∷ CS14 ∷ CX01 ∷ Sw34 ∷ CS13⁻ ∷ Sw34 ∷ Sw34 ∷ CX01 ∷ CS03 ∷ Sw34 ∷ []) (CS04 ∷ CX10 ∷ CS04⁻ ∷ Sw01 ∷ CX01 ∷ CS04 ∷ [])
  b2 = at 3 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 5 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0004 c4) ▸
       at 0 2 (CS04 ∷ Sw01 ∷ []) (lem-comm-push-CS14-sw0-R c4) ▸
       at 1 2 (CX10 ∷ Sw01 ∷ []) (sym (wl0115 c4)) ▸
       at 2 2 (CS04⁻ ∷ Sw01 ∷ []) (lem-comm-push-CSd14-sw0-R c4) ▸ done

  b3 : Chain (CS04 ∷ CX10 ∷ CS04⁻ ∷ Sw01 ∷ CX01 ∷ CS04 ∷ []) (Sw34 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ Sw34 ∷ CX10 ∷ CS14 ∷ Sw01 ∷ [])
  b3 = at 3 2 (CX10 ∷ Sw01 ∷ []) (sym (wl0115 c4)) ▸
       at 4 2 (CS14 ∷ Sw01 ∷ []) (lem-comm-push-CS04-sw0-R c4) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0004 c4) ▸
       at 2 2 (CX10 ∷ Sw34 ∷ []) (sym (c₂ (CX₁₀) (Swap ↑))) ▸
       at 4 1 (Sw34 ∷ CS03⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0004 c4) ▸ done

  b4 : Chain (Sw34 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ Sw34 ∷ CX10 ∷ CS14 ∷ Sw01 ∷ []) (Sw34 ∷ Sw23 ∷ CS02 ∷ CX10 ∷ Sw23 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ CX10 ∷ CS13 ∷ Sw34 ∷ Sw01 ∷ [])
  b4 = at 4 2 (CX10 ∷ Sw34 ∷ []) (sym (c₂ (CX₁₀) (Swap ↑))) ▸
       at 6 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0004 c4) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0003 c4) ▸
       at 3 2 (CX10 ∷ Sw23 ∷ []) (sym (c₂ (CX₁₀) (Swap))) ▸
       at 5 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b5 : Chain (Sw34 ∷ Sw23 ∷ CS02 ∷ CX10 ∷ Sw23 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ CX10 ∷ CS13 ∷ Sw34 ∷ Sw01 ∷ []) (CCZ014 ∷ Sw01 ∷ [])
  b5 = at 4 2 [] (wl0003 c4) ▸
       at 5 2 (CX10 ∷ Sw23 ∷ []) (sym (c₂ (CX₁₀) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0003 c4) ▸
       at 2 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wl0108 c4) ▸
       at 2 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (CCZ014 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm push TOFF014 sw0 R: 63 steps
lem-comm-push-TOFF014-sw0-R : WsL → ⟪ (Sw01 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff104 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-TOFF014-sw0-R c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (Sw01 ∷ Toff014 ∷ []) (Sw01 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸ done

  b1 : Chain (Sw01 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ []) (Sw01 ∷ K0 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ [])
  b1 = at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 10 2 [] (wl0003 c4) ▸
       at 1 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸ done

  b2 : Chain (Sw01 ∷ K0 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ []) (Sw01 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw34 ∷ [])
  b2 = at 4 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 4 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (Sw01 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw34 ∷ []) (K1 ∷ CS04 ∷ CX10 ∷ CS04⁻ ∷ CX10 ∷ Sw01 ∷ CS04 ∷ K0 ∷ ι ∷ [])
  b3 = at 7 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 8 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 9 2 [] (wl0004 c4) ▸
       at 0 2 (K1 ∷ Sw01 ∷ []) (sym (wl0109 c4)) ▸
       at 1 2 (CS04 ∷ Sw01 ∷ []) (lem-comm-push-CS14-sw0-R c4) ▸
       at 2 2 (CX10 ∷ Sw01 ∷ []) (sym (wl0115 c4)) ▸
       at 3 2 (CS04⁻ ∷ Sw01 ∷ []) (lem-comm-push-CSd14-sw0-R c4) ▸
       at 4 2 (CX10 ∷ Sw01 ∷ []) (sym (wl0115 c4)) ▸ done

  b4 : Chain (K1 ∷ CS04 ∷ CX10 ∷ CS04⁻ ∷ CX10 ∷ Sw01 ∷ CS04 ∷ K0 ∷ ι ∷ []) (Sw34 ∷ K1 ∷ CS03 ∷ CX10 ∷ Sw34 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ K1 ∷ ι ∷ Sw01 ∷ [])
  b4 = at 5 2 (CS14 ∷ Sw01 ∷ []) (lem-comm-push-CS04-sw0-R c4) ▸
       at 6 2 (K1 ∷ Sw01 ∷ []) (sym (wl0109 c4)) ▸
       at 7 2 (ι ∷ Sw01 ∷ []) (wl0025 c4) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 3 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0004 c4) ▸
       at 3 2 (CX10 ∷ Sw34 ∷ []) (sym (c₂ (CX₁₀) (Swap ↑))) ▸ done

  b5 : Chain (Sw34 ∷ K1 ∷ CS03 ∷ CX10 ∷ Sw34 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ K1 ∷ ι ∷ Sw01 ∷ []) (Sw34 ∷ Sw23 ∷ Sw23 ∷ K1 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw01 ∷ [])
  b5 = at 5 1 (Sw34 ∷ CS03⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0004 c4) ▸
       at 5 2 (CX10 ∷ Sw34 ∷ []) (sym (c₂ (CX₁₀) (Swap ↑))) ▸
       at 7 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0004 c4) ▸
       at 7 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 8 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸ done

  b6 : Chain (Sw34 ∷ Sw23 ∷ Sw23 ∷ K1 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw01 ∷ []) (Sw34 ∷ Sw23 ∷ K1 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw01 ∷ [])
  b6 = at 2 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0003 c4) ▸
       at 4 2 (CX10 ∷ Sw23 ∷ []) (sym (c₂ (CX₁₀) (Swap))) ▸
       at 6 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0003 c4) ▸
       at 6 2 (CX10 ∷ Sw23 ∷ []) (sym (c₂ (CX₁₀) (Swap))) ▸
       at 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b7 : Chain (Sw34 ∷ Sw23 ∷ K1 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw01 ∷ []) (Toff104 ∷ Sw01 ∷ [])
  b7 = at 7 2 [] (wl0003 c4) ▸
       at 8 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 2 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (wl0116 c4) ▸
       at 2 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff103 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff104 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm push BOX(0;13) sw0 R: 3 steps
lem-comm-push-BOX⟨0·13⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Bx0-13 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-03 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·13⟩-sw0-R c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-13 ∷ []) (Bx1-03 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ13 ∷ []) (refl) ▸
       at 0 2 (CZ03 ∷ Sw01 ∷ []) (sym (wl0049 c4)) ▸
       at 0 1 (Bx1-03 ∷ []) (refl) ▸ done


-- comm push BOX(1;023) sw0 R: 8 steps
lem-comm-push-BOX⟨1·023⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Bx1-023 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-123 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨1·023⟩-sw0-R c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-023 ∷ []) (Bx0-123 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0103 c4)) ▸
       at 1 2 (Toff012 ∷ Sw01 ∷ []) (wl0104 c4) ▸
       at 2 2 (Bx1-03 ∷ Sw01 ∷ []) (lem-comm-push-BOX⟨0·13⟩-sw0-R c4) ▸
       at 3 2 (Toff012 ∷ Sw01 ∷ []) (wl0104 c4) ▸
       at 4 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0103 c4)) ▸
       at 5 2 (Bx1-03 ∷ Sw01 ∷ []) (lem-comm-push-BOX⟨0·13⟩-sw0-R c4) ▸
       at 0 6 (Bx0-123 ∷ []) (refl) ▸ done


-- comm push BOX(0;1423) sw0 R: 8 steps
lem-comm-push-BOX⟨0·1423⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·1423⟩-sw0-R c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-1423 ∷ []) (Bx1-0423 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff014 ∷ Bx1-023 ∷ Toff014 ∷ CCZ014 ∷ Bx1-023 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw01 ∷ []) (lem-comm-push-CCZ014-sw0-R c4) ▸
       at 1 2 (Toff104 ∷ Sw01 ∷ []) (lem-comm-push-TOFF014-sw0-R c4) ▸
       at 2 2 (Bx0-123 ∷ Sw01 ∷ []) (lem-comm-push-BOX⟨1·023⟩-sw0-R c4) ▸
       at 3 2 (Toff104 ∷ Sw01 ∷ []) (lem-comm-push-TOFF014-sw0-R c4) ▸
       at 4 2 (CCZ014 ∷ Sw01 ∷ []) (lem-comm-push-CCZ014-sw0-R c4) ▸
       at 5 2 (Bx0-123 ∷ Sw01 ∷ []) (lem-comm-push-BOX⟨1·023⟩-sw0-R c4) ▸
       at 0 6 (Bx1-0423 ∷ []) (refl) ▸ done


-- comm push SBOX(0;1;3;2) sw0 R: 3 steps
lem-comm-push-SBOX⟨0·1·3·2⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Sb0-1-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-3-2 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨0·1·3·2⟩-sw0-R c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb0-1-3-2 ∷ []) (Sb1-0-3-2 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS13 ∷ []) (refl) ▸
       at 0 2 (CS03 ∷ Sw01 ∷ []) (sym (wl0015 c4)) ▸
       at 0 1 (Sb1-0-3-2 ∷ []) (refl) ▸ done


-- comm push SBOXd(0;1;3;2) sw0 R: 3 steps
lem-comm-push-SBOXd⟨0·1·3·2⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Sb⁻0-1-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-3-2 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨0·1·3·2⟩-sw0-R c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻0-1-3-2 ∷ []) (Sb⁻1-0-3-2 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS13⁻ ∷ []) (refl) ▸
       at 0 2 (CS03⁻ ∷ Sw01 ∷ []) (sym (wl0042 c4)) ▸
       at 0 1 (Sb⁻1-0-3-2 ∷ []) (refl) ▸ done


-- comm push SBOX(0;1;42;3) sw0 R: 7 steps
lem-comm-push-SBOX⟨0·1·42·3⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨0·1·42·3⟩-sw0-R c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb0-1-42-3 ∷ []) (Sb1-0-42-3 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 0 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-comm-push-BOX⟨0·1423⟩-sw0-R c4) ▸
       at 1 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 2 2 (Sb1-0-3-2 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·1·3·2⟩-sw0-R c4) ▸
       at 3 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 4 2 (Sb⁻1-0-3-2 ∷ Sw01 ∷ []) (lem-comm-push-SBOXd⟨0·1·3·2⟩-sw0-R c4) ▸
       at 0 5 (Sb1-0-42-3 ∷ []) (refl) ▸ done


-- comm push CK40 sw1 R: 5 steps
lem-comm-push-CK40-sw1-R : WsL → ⟪ (Sw12 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-CK40-sw1-R c4 = run b0
  where
  b0 : Chain (Sw12 ∷ CK40 ∷ []) (CK40 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 1 2 (CK30 ∷ Sw12 ∷ []) (sym (wl0088 c4)) ▸
       at 2 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 0 3 (CK40 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm push BOX(1;03) sw1 R: 3 steps
lem-comm-push-BOX⟨1·03⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Bx1-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-03 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨1·03⟩-sw1-R c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-03 ∷ []) (Bx2-03 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ03 ∷ []) (refl) ▸
       at 0 2 (CZ03 ∷ Sw12 ∷ []) (sym (wl0079 c4)) ▸
       at 0 1 (Bx2-03 ∷ []) (refl) ▸ done


-- comm push BOX(0;123) sw1 R: 8 steps
lem-comm-push-BOX⟨0·123⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Bx0-123 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-213 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·123⟩-sw1-R c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-123 ∷ []) (Bx0-213 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ Bx1-03 ∷ Toff012 ∷ CCZ012 ∷ Bx1-03 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0101 c4)) ▸
       at 1 2 (Toff012 ∷ Sw12 ∷ []) (wl0102 c4) ▸
       at 2 2 (Bx2-03 ∷ Sw12 ∷ []) (lem-comm-push-BOX⟨1·03⟩-sw1-R c4) ▸
       at 3 2 (Toff012 ∷ Sw12 ∷ []) (wl0102 c4) ▸
       at 4 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0101 c4)) ▸
       at 5 2 (Bx2-03 ∷ Sw12 ∷ []) (lem-comm-push-BOX⟨1·03⟩-sw1-R c4) ▸
       at 0 6 (Bx0-213 ∷ []) (refl) ▸ done


-- comm push BOX(1;0423) sw1 R: 12 steps
lem-comm-push-BOX⟨1·0423⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Bx1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨1·0423⟩-sw1-R c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw12 ∷ Bx1-0423 ∷ []) (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ Sw12 ∷ CCZ014 ∷ Bx0-123 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff104 ∷ Bx0-123 ∷ Toff104 ∷ CCZ014 ∷ Bx0-123 ∷ []) (refl) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 0 3 (CCZ024 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 1 3 (Toff204 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Bx0-213 ∷ Sw12 ∷ []) (lem-comm-push-BOX⟨0·123⟩-sw1-R c4) ▸
       at 5 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 3 3 (Toff204 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ Sw12 ∷ CCZ014 ∷ Bx0-123 ∷ []) (Bx2-0413 ∷ Sw12 ∷ [])
  b1 = at 6 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 4 3 (CCZ024 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Bx0-213 ∷ Sw12 ∷ []) (lem-comm-push-BOX⟨0·123⟩-sw1-R c4) ▸
       at 0 6 (Bx2-0413 ∷ []) (refl) ▸ done


-- comm push SBOX(1;0;3;2) sw1 R: 3 steps
lem-comm-push-SBOX⟨1·0·3·2⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Sb1-0-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-3-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨1·0·3·2⟩-sw1-R c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb1-0-3-2 ∷ []) (Sb2-0-3-1 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS03 ∷ []) (refl) ▸
       at 0 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 0 1 (Sb2-0-3-1 ∷ []) (refl) ▸ done


-- comm push SBOXd(1;0;3;2) sw1 R: 3 steps
lem-comm-push-SBOXd⟨1·0·3·2⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Sb⁻1-0-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-3-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-SBOXd⟨1·0·3·2⟩-sw1-R c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻1-0-3-2 ∷ []) (Sb⁻2-0-3-1 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 2 (CS03⁻ ∷ Sw12 ∷ []) (sym (wl0043 c4)) ▸
       at 0 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸ done


-- comm push SBOX(1;0;42;3) sw1 R: 7 steps
lem-comm-push-SBOX⟨1·0·42·3⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨1·0·42·3⟩-sw1-R c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb1-0-42-3 ∷ []) (Sb2-0-41-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (refl) ▸
       at 0 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-comm-push-BOX⟨1·0423⟩-sw1-R c4) ▸
       at 1 2 (Toff314 ∷ Sw12 ∷ []) (wl0038 c4) ▸
       at 2 2 (Sb2-0-3-1 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·0·3·2⟩-sw1-R c4) ▸
       at 3 2 (Toff314 ∷ Sw12 ∷ []) (wl0038 c4) ▸
       at 4 2 (Sb⁻2-0-3-1 ∷ Sw12 ∷ []) (lem-comm-push-SBOXd⟨1·0·3·2⟩-sw1-R c4) ▸
       at 0 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done


-- comm CCZ014 CX32: 9 steps
lem-comm-CCZ014-CX32 : WsL → ⟪ (CCZ014 ∷ CX32 ∷ []) ⟫ʷ ≈ ⟪ (CX32 ∷ CCZ014 ∷ []) ⟫ʷ
lem-comm-CCZ014-CX32 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ014 ∷ CX32 ∷ []) (CX32 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 4 3 (CX42 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX43 ∷ Sw23 ∷ []) (sym (wl0059 c4)) ▸
       at 2 2 (CX43 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CX₁₀)) ▸
       at 1 2 (CX42 ∷ Sw23 ∷ []) (sym (wl0058 c4)) ▸
       at 1 1 (Sw34 ∷ CX32 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0004 c4) ▸ done

  b1 : Chain (CX32 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ []) (CX32 ∷ CCZ014 ∷ [])
  b1 = at 1 5 (CCZ014 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm push CCZ124 sw0 L: 46 steps
lem-comm-push-CCZ124-sw0-L : WsL → ⟪ (CCZ124 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CCZ024 ∷ []) ⟫ʷ
lem-comm-push-CCZ124-sw0-L c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (run b5)))))
  where
  b0 : Chain (CCZ124 ∷ Sw01 ∷ []) (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ Sw01 ∷ [])
  b0 = at 0 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 0 3 (CS24 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 4 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸ done

  b1 : Chain (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ Sw01 ∷ []) (Sw01 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ [])
  b1 = at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 4 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0004 c4) ▸
       at 4 2 (Sw01 ∷ CS04 ∷ []) (lem-comm-push-CS14-sw0-L c4) ▸
       at 3 2 (Sw01 ∷ CX02 ∷ []) (wl0117 c4) ▸
       at 2 2 (Sw01 ∷ CS24⁻ ∷ []) (sym (c₂ (Swap) (Swap ↑ • (CS • CS • CS) • Swap ↑))) ▸
       at 1 2 (Sw01 ∷ CX02 ∷ []) (wl0117 c4) ▸
       at 0 2 (Sw01 ∷ CS24 ∷ []) (sym (c₂ (Swap) (Swap ↑ • CS • Swap ↑))) ▸ done

  b2 : Chain (Sw01 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ []) (Sw01 ∷ Sw12 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw12 ∷ [])
  b2 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 2 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 c4)) ▸
       at 4 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0006 c4) ▸
       at 4 2 (CS14⁻ ∷ Sw12 ∷ []) (sym (wl0014 c4)) ▸
       at 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0006 c4) ▸
       at 6 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R c4) ▸ done

  b3 : Chain (Sw01 ∷ Sw12 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw12 ∷ []) (Sw01 ∷ Sw12 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw34 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ [])
  b3 = at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 4 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0004 c4) ▸
       at 4 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 6 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0004 c4) ▸
       at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (Sw01 ∷ Sw12 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw34 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ []) (Sw01 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ [])
  b4 = at 7 2 [] (wl0004 c4) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0003 c4) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0003 c4) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸ done

  b5 : Chain (Sw01 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ []) (Sw01 ∷ CCZ024 ∷ [])
  b5 = at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0003 c4) ▸
       at 4 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (CCZ014 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (CCZ024 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm push TOFF412 sw0 L: 62 steps
lem-comm-push-TOFF412-sw0-L : WsL → ⟪ (Toff412 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Toff402 ∷ []) ⟫ʷ
lem-comm-push-TOFF412-sw0-L c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (Toff412 ∷ Sw01 ∷ []) (K4 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Sw34 ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ Sw34 ∷ Sw01 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Toff312 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (K4 ∷ Sw34 ∷ []) (sym (wl0065 c4)) ▸
       at 3 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 3 (CS24 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (K4 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Sw34 ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ Sw34 ∷ Sw01 ∷ []) (K4 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Sw01 ∷ K4 ∷ ι1 ∷ [])
  b1 = at 4 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 5 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K4 ∷ Sw34 ∷ []) (sym (wl0065 c4)) ▸
       at 7 2 (ι1 ∷ Sw34 ∷ []) (sym (c₂ (iI ↑) (Swap ↑))) ▸
       at 8 2 [] (wl0004 c4) ▸
       at 7 2 (Sw01 ∷ ι1 ∷ []) (sym (wl0118 c4)) ▸
       at 6 2 (Sw01 ∷ K4 ∷ []) (sym (c₂ (Swap) (K ↑ ↑))) ▸ done

  b2 : Chain (K4 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Sw01 ∷ K4 ∷ ι1 ∷ []) (Sw01 ∷ Sw12 ∷ K4 ∷ Sw12 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K4 ∷ ι1 ∷ [])
  b2 = at 5 2 (Sw01 ∷ CS04 ∷ []) (lem-comm-push-CS14-sw0-L c4) ▸
       at 4 2 (Sw01 ∷ CX02 ∷ []) (wl0117 c4) ▸
       at 3 2 (Sw01 ∷ CS24⁻ ∷ []) (sym (c₂ (Swap) (Swap ↑ • (CS • CS • CS) • Swap ↑))) ▸
       at 2 2 (Sw01 ∷ CX02 ∷ []) (wl0117 c4) ▸
       at 1 2 (Sw01 ∷ CS24 ∷ []) (sym (c₂ (Swap) (Swap ↑ • CS • Swap ↑))) ▸
       at 0 2 (Sw01 ∷ K4 ∷ []) (sym (c₂ (Swap) (K ↑ ↑))) ▸
       at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 2 2 (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑)) ▸ done

  b3 : Chain (Sw01 ∷ Sw12 ∷ K4 ∷ Sw12 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K4 ∷ ι1 ∷ []) (Sw01 ∷ Sw12 ∷ K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K4 ∷ Sw12 ∷ ι1 ∷ [])
  b3 = at 3 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 c4)) ▸
       at 5 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0006 c4) ▸
       at 5 2 (CS14⁻ ∷ Sw12 ∷ []) (sym (wl0014 c4)) ▸
       at 7 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0006 c4) ▸
       at 7 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R c4) ▸
       at 8 2 (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑)) ▸ done

  b4 : Chain (Sw01 ∷ Sw12 ∷ K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K4 ∷ Sw12 ∷ ι1 ∷ []) (Sw01 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw34 ∷ CX01 ∷ CS04 ∷ K4 ∷ ι1 ∷ Sw12 ∷ [])
  b4 = at 9 2 (ι1 ∷ Sw12 ∷ []) (wl0119 c4) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 2 (K3 ∷ Sw34 ∷ []) (sym (wl0066 c4)) ▸
       at 5 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0004 c4) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0004 c4) ▸ done

  b5 : Chain (Sw01 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw34 ∷ CX01 ∷ CS04 ∷ K4 ∷ ι1 ∷ Sw12 ∷ []) (Sw01 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K2 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι1 ∷ Sw34 ∷ Sw12 ∷ [])
  b5 = at 7 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 9 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0004 c4) ▸
       at 9 2 (K3 ∷ Sw34 ∷ []) (sym (wl0066 c4)) ▸
       at 10 2 (ι1 ∷ Sw34 ∷ []) (sym (c₂ (iI ↑) (Swap ↑))) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 2 (K2 ∷ Sw23 ∷ []) (sym (wl0067 c4)) ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b6 : Chain (Sw01 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K2 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι1 ∷ Sw34 ∷ Sw12 ∷ []) (Sw01 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ Sw23 ∷ ι1 ∷ Sw34 ∷ Sw12 ∷ [])
  b6 = at 5 2 [] (wl0003 c4) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0003 c4) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (wl0003 c4) ▸
       at 10 2 (K2 ∷ Sw23 ∷ []) (sym (wl0067 c4)) ▸ done

  b7 : Chain (Sw01 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ Sw23 ∷ ι1 ∷ Sw34 ∷ Sw12 ∷ []) (Sw01 ∷ Toff402 ∷ [])
  b7 = at 11 2 (ι1 ∷ Sw23 ∷ []) (sym (c₂ (iI ↑) (Swap))) ▸
       at 4 8 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (sym (wl0120 c4)) ▸
       at 4 8 (Toff201 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (Toff301 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff401 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff402 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm push BOX(4;213) sw0 L: 8 steps
lem-comm-push-BOX⟨4·213⟩-sw0-L : WsL → ⟪ (Bx4-213 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Bx4-203 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨4·213⟩-sw0-L c4 = run b0
  where
  b0 : Chain (Bx4-213 ∷ Sw01 ∷ []) (Sw01 ∷ Bx4-203 ∷ [])
  b0 = at 0 1 (CCZ124 ∷ Toff412 ∷ Bx2-43 ∷ Toff412 ∷ CCZ124 ∷ Bx2-43 ∷ []) (refl) ▸
       at 5 2 (Sw01 ∷ Bx2-43 ∷ []) (sym (c₂ (Swap) (CZ ↑))) ▸
       at 4 2 (Sw01 ∷ CCZ024 ∷ []) (lem-comm-push-CCZ124-sw0-L c4) ▸
       at 3 2 (Sw01 ∷ Toff402 ∷ []) (lem-comm-push-TOFF412-sw0-L c4) ▸
       at 2 2 (Sw01 ∷ Bx2-43 ∷ []) (sym (c₂ (Swap) (CZ ↑))) ▸
       at 1 2 (Sw01 ∷ Toff402 ∷ []) (lem-comm-push-TOFF412-sw0-L c4) ▸
       at 0 2 (Sw01 ∷ CCZ024 ∷ []) (lem-comm-push-CCZ124-sw0-L c4) ▸
       at 1 6 (Bx4-203 ∷ []) (refl) ▸ done


-- comm push BOX(2;4013) sw0 L: 8 steps
lem-comm-push-BOX⟨2·4013⟩-sw0-L : WsL → ⟪ (Bx2-4013 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Bx2-4103 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨2·4013⟩-sw0-L c4 = run b0
  where
  b0 : Chain (Bx2-4013 ∷ Sw01 ∷ []) (Sw01 ∷ Bx2-4103 ∷ [])
  b0 = at 0 1 (CCZ024 ∷ Toff204 ∷ Bx4-213 ∷ Toff204 ∷ CCZ024 ∷ Bx4-213 ∷ []) (refl) ▸
       at 5 2 (Sw01 ∷ Bx4-203 ∷ []) (lem-comm-push-BOX⟨4·213⟩-sw0-L c4) ▸
       at 4 2 (Sw01 ∷ CCZ124 ∷ []) (lem-comm-push-CCZ024-sw0-L c4) ▸
       at 3 2 (Sw01 ∷ Toff214 ∷ []) (lem-comm-push-TOFF204-sw0-L c4) ▸
       at 2 2 (Sw01 ∷ Bx4-203 ∷ []) (lem-comm-push-BOX⟨4·213⟩-sw0-L c4) ▸
       at 1 2 (Sw01 ∷ Toff214 ∷ []) (lem-comm-push-TOFF204-sw0-L c4) ▸
       at 0 2 (Sw01 ∷ CCZ124 ∷ []) (lem-comm-push-CCZ024-sw0-L c4) ▸
       at 1 6 (Bx2-4103 ∷ []) (refl) ▸ done


-- comm push SBOX(2;4;01;3) sw0 L: 7 steps
lem-comm-push-SBOX⟨2·4·01·3⟩-sw0-L : WsL → ⟪ (Sb2-4-01-3 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Sb2-4-10-3 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨2·4·01·3⟩-sw0-L c4 = run b0
  where
  b0 : Chain (Sb2-4-01-3 ∷ Sw01 ∷ []) (Sw01 ∷ Sb2-4-10-3 ∷ [])
  b0 = at 0 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 4 2 (Sw01 ∷ Sb⁻2-4-3-1 ∷ []) (sym (c₂ (Swap) ((CS • CS • CS) ↑))) ▸
       at 3 2 (Sw01 ∷ Toff301 ∷ []) (sym (wl0121 c4)) ▸
       at 2 2 (Sw01 ∷ Sb2-4-3-1 ∷ []) (sym (c₂ (Swap) (CS ↑))) ▸
       at 1 2 (Sw01 ∷ Toff301 ∷ []) (sym (wl0121 c4)) ▸
       at 0 2 (Sw01 ∷ Bx2-4103 ∷ []) (lem-comm-push-BOX⟨2·4013⟩-sw0-L c4) ▸
       at 1 5 (Sb2-4-10-3 ∷ []) (refl) ▸ done


-- comm push BOX(4;203) sw1 L: 12 steps
lem-comm-push-BOX⟨4·203⟩-sw1-L : WsL → ⟪ (Bx4-203 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Bx4-103 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨4·203⟩-sw1-L c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx4-203 ∷ Sw12 ∷ []) (CCZ024 ∷ Sw12 ∷ Toff401 ∷ Sw12 ∷ Sw12 ∷ Bx2-43 ∷ Toff401 ∷ CCZ014 ∷ Bx2-43 ∷ [])
  b0 = at 0 1 (CCZ024 ∷ Toff402 ∷ Bx2-43 ∷ Toff402 ∷ CCZ024 ∷ Bx2-43 ∷ []) (refl) ▸
       at 5 2 (Sw12 ∷ Bx2-43 ∷ []) (sym (c₃ (Swap ↑) (CZ))) ▸
       at 4 1 (Sw12 ∷ CCZ014 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0006 c4) ▸
       at 3 1 (Sw12 ∷ Toff401 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0006 c4) ▸
       at 2 2 (Sw12 ∷ Bx2-43 ∷ []) (sym (c₃ (Swap ↑) (CZ))) ▸
       at 1 1 (Sw12 ∷ Toff401 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (CCZ024 ∷ Sw12 ∷ Toff401 ∷ Sw12 ∷ Sw12 ∷ Bx2-43 ∷ Toff401 ∷ CCZ014 ∷ Bx2-43 ∷ []) (Sw12 ∷ Bx4-103 ∷ [])
  b1 = at 3 2 [] (wl0006 c4) ▸
       at 0 1 (Sw12 ∷ CCZ014 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0006 c4) ▸
       at 1 6 (Bx4-103 ∷ []) (refl) ▸ done


-- comm push BOX(2;4103) sw1 L: 8 steps
lem-comm-push-BOX⟨2·4103⟩-sw1-L : WsL → ⟪ (Bx2-4103 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Bx1-4203 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨2·4103⟩-sw1-L c4 = run b0
  where
  b0 : Chain (Bx2-4103 ∷ Sw12 ∷ []) (Sw12 ∷ Bx1-4203 ∷ [])
  b0 = at 0 1 (CCZ124 ∷ Toff214 ∷ Bx4-203 ∷ Toff214 ∷ CCZ124 ∷ Bx4-203 ∷ []) (refl) ▸
       at 5 2 (Sw12 ∷ Bx4-103 ∷ []) (lem-comm-push-BOX⟨4·203⟩-sw1-L c4) ▸
       at 4 2 (Sw12 ∷ CCZ124 ∷ []) (wl0122 c4) ▸
       at 3 2 (Sw12 ∷ Toff124 ∷ []) (sym (wl0123 c4)) ▸
       at 2 2 (Sw12 ∷ Bx4-103 ∷ []) (lem-comm-push-BOX⟨4·203⟩-sw1-L c4) ▸
       at 1 2 (Sw12 ∷ Toff124 ∷ []) (sym (wl0123 c4)) ▸
       at 0 2 (Sw12 ∷ CCZ124 ∷ []) (wl0122 c4) ▸
       at 1 6 (Bx1-4203 ∷ []) (refl) ▸ done


-- comm push SBOX(2;4;10;3) sw1 L: 9 steps
lem-comm-push-SBOX⟨2·4·10·3⟩-sw1-L : WsL → ⟪ (Sb2-4-10-3 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sb1-4-20-3 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨2·4·10·3⟩-sw1-L c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb2-4-10-3 ∷ Sw12 ∷ []) (Sw12 ∷ Bx1-4203 ∷ Toff302 ∷ Sb2-4-3-0 ∷ Toff302 ∷ Sb⁻2-4-3-0 ∷ [])
  b0 = at 0 1 (Bx2-4103 ∷ Toff301 ∷ Sb2-4-3-0 ∷ Toff301 ∷ Sb⁻2-4-3-0 ∷ []) (refl) ▸
       at 4 2 (Sw12 ∷ Sb⁻2-4-3-0 ∷ []) (sym (c₃ (Swap ↑) (CS • CS • CS))) ▸
       at 3 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 4 3 (Toff302 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw12 ∷ Sb2-4-3-0 ∷ []) (sym (c₃ (Swap ↑) (CS))) ▸
       at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 2 3 (Toff302 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ Bx1-4203 ∷ []) (lem-comm-push-BOX⟨2·4103⟩-sw1-L c4) ▸ done

  b1 : Chain (Sw12 ∷ Bx1-4203 ∷ Toff302 ∷ Sb2-4-3-0 ∷ Toff302 ∷ Sb⁻2-4-3-0 ∷ []) (Sw12 ∷ Sb1-4-20-3 ∷ [])
  b1 = at 1 5 (Sb1-4-20-3 ∷ []) (refl) ▸ done


-- comm push TOFF401 sw0 L: 63 steps
lem-comm-push-TOFF401-sw0-L : WsL → ⟪ (Toff401 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Toff401 ∷ []) ⟫ʷ
lem-comm-push-TOFF401-sw0-L c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (Toff401 ∷ Sw01 ∷ []) (Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw01 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Toff301 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (K3 ∷ Sw23 ∷ []) (sym (wl0064 c4)) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸ done

  b1 : Chain (Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw01 ∷ []) (K4 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw01 ∷ [])
  b1 = at 4 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K3 ∷ Sw23 ∷ []) (sym (wl0064 c4)) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 9 2 [] (wl0003 c4) ▸
       at 0 2 (K4 ∷ Sw34 ∷ []) (sym (wl0065 c4)) ▸ done

  b2 : Chain (K4 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw01 ∷ []) (K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw34 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw01 ∷ [])
  b2 = at 3 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 5 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw34 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw01 ∷ []) (K4 ∷ CS14 ∷ CX01 ∷ Sw01 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ K4 ∷ ι ∷ [])
  b3 = at 6 2 (K4 ∷ Sw34 ∷ []) (sym (wl0065 c4)) ▸
       at 7 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 8 2 [] (wl0004 c4) ▸
       at 7 2 (Sw01 ∷ ι ∷ []) (sym (wl0025 c4)) ▸
       at 6 2 (Sw01 ∷ K4 ∷ []) (sym (c₂ (Swap) (K ↑ ↑))) ▸
       at 5 2 (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L c4) ▸
       at 4 2 (Sw01 ∷ CX10 ∷ []) (wl0107 c4) ▸
       at 3 2 (Sw01 ∷ CS04⁻ ∷ []) (lem-comm-push-CSd14-sw0-L c4) ▸ done

  b4 : Chain (K4 ∷ CS14 ∷ CX01 ∷ Sw01 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ K4 ∷ ι ∷ []) (Sw01 ∷ Sw34 ∷ K3 ∷ CS03 ∷ CX10 ∷ Sw34 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ K4 ∷ ι ∷ [])
  b4 = at 2 2 (Sw01 ∷ CX10 ∷ []) (wl0107 c4) ▸
       at 1 2 (Sw01 ∷ CS04 ∷ []) (lem-comm-push-CS14-sw0-L c4) ▸
       at 0 2 (Sw01 ∷ K4 ∷ []) (sym (c₂ (Swap) (K ↑ ↑))) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 2 (K3 ∷ Sw34 ∷ []) (sym (wl0066 c4)) ▸
       at 4 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0004 c4) ▸
       at 4 2 (CX10 ∷ Sw34 ∷ []) (sym (c₂ (CX₁₀) (Swap ↑))) ▸ done

  b5 : Chain (Sw01 ∷ Sw34 ∷ K3 ∷ CS03 ∷ CX10 ∷ Sw34 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ K4 ∷ ι ∷ []) (Sw01 ∷ Sw34 ∷ Sw23 ∷ Sw23 ∷ K3 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K3 ∷ ι ∷ Sw34 ∷ [])
  b5 = at 6 1 (Sw34 ∷ CS03⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0004 c4) ▸
       at 6 2 (CX10 ∷ Sw34 ∷ []) (sym (c₂ (CX₁₀) (Swap ↑))) ▸
       at 8 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0004 c4) ▸
       at 8 2 (K3 ∷ Sw34 ∷ []) (sym (wl0066 c4)) ▸
       at 9 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸ done

  b6 : Chain (Sw01 ∷ Sw34 ∷ Sw23 ∷ Sw23 ∷ K3 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K3 ∷ ι ∷ Sw34 ∷ []) (Sw01 ∷ Sw34 ∷ Sw23 ∷ K2 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ K3 ∷ ι ∷ Sw34 ∷ [])
  b6 = at 3 2 (K2 ∷ Sw23 ∷ []) (sym (wl0067 c4)) ▸
       at 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0003 c4) ▸
       at 5 2 (CX10 ∷ Sw23 ∷ []) (sym (c₂ (CX₁₀) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0003 c4) ▸
       at 7 2 (CX10 ∷ Sw23 ∷ []) (sym (c₂ (CX₁₀) (Swap))) ▸
       at 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b7 : Chain (Sw01 ∷ Sw34 ∷ Sw23 ∷ K2 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ K3 ∷ ι ∷ Sw34 ∷ []) (Sw01 ∷ Toff401 ∷ [])
  b7 = at 8 2 [] (wl0003 c4) ▸
       at 9 2 (K2 ∷ Sw23 ∷ []) (sym (wl0067 c4)) ▸
       at 10 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 3 8 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (wl0124 c4) ▸
       at 3 8 (Toff201 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff301 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff401 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm push BOX(4;103) sw0 L: 8 steps
lem-comm-push-BOX⟨4·103⟩-sw0-L : WsL → ⟪ (Bx4-103 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Bx4-013 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨4·103⟩-sw0-L c4 = run b0
  where
  b0 : Chain (Bx4-103 ∷ Sw01 ∷ []) (Sw01 ∷ Bx4-013 ∷ [])
  b0 = at 0 1 (CCZ014 ∷ Toff401 ∷ Bx1-43 ∷ Toff401 ∷ CCZ014 ∷ Bx1-43 ∷ []) (refl) ▸
       at 5 2 (Sw01 ∷ Bx1-43 ∷ []) (sym (c₂ (Swap) (CZ ↑))) ▸
       at 4 2 (Sw01 ∷ CCZ014 ∷ []) (lem-comm-push-CCZ014-sw0-L c4) ▸
       at 3 2 (Sw01 ∷ Toff401 ∷ []) (lem-comm-push-TOFF401-sw0-L c4) ▸
       at 2 2 (Sw01 ∷ Bx1-43 ∷ []) (sym (c₂ (Swap) (CZ ↑))) ▸
       at 1 2 (Sw01 ∷ Toff401 ∷ []) (lem-comm-push-TOFF401-sw0-L c4) ▸
       at 0 2 (Sw01 ∷ CCZ014 ∷ []) (lem-comm-push-CCZ014-sw0-L c4) ▸
       at 1 6 (Bx4-013 ∷ []) (refl) ▸ done


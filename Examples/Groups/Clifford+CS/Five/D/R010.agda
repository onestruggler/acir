{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R010 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL ; wl0003 ; wl0004 ; wl0006 ; wl0038 ; wl0083 ; wl0111 ; wl0127 ; wl0148 ; wl0150)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-push-SBOXd⟨0·1·2·3⟩-sw1-L ; lem-comm-push-SBOXd⟨0·1·2·3⟩-sw2-R ; lem-comm-push-SBOXd⟨0·1·3·2⟩-sw0-R ; lem-comm-push-SBOXd⟨0·1·3·2⟩-sw2-L ; lem-comm-push-SBOXd⟨0·2·1·3⟩-sw0-R ; lem-comm-push-SBOXd⟨0·2·1·3⟩-sw1-R ; lem-comm-push-SBOXd⟨0·2·1·3⟩-sw2-R ; lem-comm-push-SBOXd⟨0·3·1·2⟩-sw2-L ; lem-comm-push-SBOXd⟨0·4·1·2⟩-sw1-R ; lem-comm-push-SBOXd⟨0·4·2·1⟩-sw1-L ; lem-comm-push-SBOXd⟨1·0·3·2⟩-sw0-L ; lem-comm-push-SBOXd⟨1·0·3·2⟩-sw1-R ; lem-comm-push-SBOXd⟨1·2·0·3⟩-sw1-R ; lem-comm-push-SBOXd⟨2·0·3·1⟩-sw1-L ; lem-comm-push-SBOXd⟨2·0·3·1⟩-sw2-R ; lem-comm-push-SBOXd⟨4·0·3·1⟩-sw1-R ; lem-comm-push-SBOXd⟨4·1·0·3⟩-sw1-R ; lem-comm-push-SBOXd⟨4·2·0·3⟩-sw0-R ; lem-comm-push-SBOX⟨0·1·2·3⟩-sw1-L ; lem-comm-push-SBOX⟨0·1·2·3⟩-sw2-R ; lem-comm-push-SBOX⟨0·1·3·2⟩-sw0-R ; lem-comm-push-SBOX⟨0·1·3·2⟩-sw2-L ; lem-comm-push-SBOX⟨0·2·1·3⟩-sw0-R ; lem-comm-push-SBOX⟨0·2·1·3⟩-sw1-R ; lem-comm-push-SBOX⟨0·2·1·3⟩-sw2-R ; lem-comm-push-SBOX⟨0·3·1·2⟩-sw2-L ; lem-comm-push-SBOX⟨0·4·1·2⟩-sw1-R ; lem-comm-push-SBOX⟨0·4·2·1⟩-sw1-L ; lem-comm-push-SBOX⟨1·0·3·2⟩-sw0-L ; lem-comm-push-SBOX⟨1·0·3·2⟩-sw1-R ; lem-comm-push-SBOX⟨1·2·0·3⟩-sw1-R ; lem-comm-push-SBOX⟨2·0·3·1⟩-sw1-L ; lem-comm-push-SBOX⟨2·0·3·1⟩-sw2-R ; lem-comm-push-SBOX⟨4·0·3·1⟩-sw1-R ; lem-comm-push-SBOX⟨4·1·0·3⟩-sw1-R ; lem-comm-push-SBOX⟨4·2·0·3⟩-sw0-R)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-comm-push-CCZ024-sw0-L ; lem-comm-push-TOFF204-sw0-L)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-comm-push-CCZ014-sw0-R ; lem-comm-push-CCZ034-sw3-L ; lem-comm-push-CCZ034-sw3-R ; lem-comm-push-CCZ124-sw0-L ; lem-comm-push-TOFF034-sw1-R ; lem-comm-push-TOFF034-sw3-L ; lem-comm-push-TOFF034-sw3-R ; lem-comm-push-TOFF124-sw0-L)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-comm-push-CCZ024-sw0-R ; lem-comm-push-CCZ124-sw0-R ; lem-comm-push-TOFF024-sw0-R ; lem-comm-push-TOFF134-sw0-R ; lem-comm-push-TOFF214-sw0-R ; lem-comm-push-TOFF401-sw0-R)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-comm-push-BOX⟨0·1423⟩-sw0-R ; lem-comm-push-BOX⟨0·1423⟩-sw2-L ; lem-comm-push-BOX⟨0·1432⟩-sw1-L ; lem-comm-push-BOX⟨0·1432⟩-sw2-R ; lem-comm-push-BOX⟨0·2431⟩-sw0-R ; lem-comm-push-BOX⟨0·2431⟩-sw1-R ; lem-comm-push-BOX⟨0·2431⟩-sw2-R ; lem-comm-push-BOX⟨0·3421⟩-sw2-L ; lem-comm-push-BOX⟨0·412⟩-sw2-R ; lem-comm-push-BOX⟨0·423⟩-sw0-R ; lem-comm-push-BOX⟨0·4312⟩-sw1-L ; lem-comm-push-BOX⟨0·4321⟩-sw1-R ; lem-comm-push-BOX⟨1·0423⟩-sw0-L ; lem-comm-push-BOX⟨1·0423⟩-sw1-R ; lem-comm-push-BOX⟨1·2430⟩-sw1-R ; lem-comm-push-BOX⟨2·0413⟩-sw1-L ; lem-comm-push-BOX⟨2·0413⟩-sw2-R ; lem-comm-push-BOX⟨3·021⟩-sw3-R ; lem-comm-push-BOX⟨3·0412⟩-sw3-R ; lem-comm-push-BOX⟨4·012⟩-sw2-R ; lem-comm-push-BOX⟨4·013⟩-sw0-R ; lem-comm-push-BOX⟨4·013⟩-sw2-L ; lem-comm-push-BOX⟨4·0213⟩-sw1-R ; lem-comm-push-BOX⟨4·021⟩-sw3-L ; lem-comm-push-BOX⟨4·103⟩-sw0-L ; lem-comm-push-BOX⟨4·1230⟩-sw1-R ; lem-comm-push-BOX⟨4·203⟩-sw0-R ; lem-comm-push-BOX⟨4·2130⟩-sw0-R ; lem-comm-push-BOX⟨4·213⟩-sw0-L)

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

-- comm push SBOX(0;4;32;1) sw1 R: 7 steps
lem-comm-push-SBOX⟨0·4·32·1⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Sb0-4-32-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-4-31-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨0·4·32·1⟩-sw1-R c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb0-4-32-1 ∷ []) (Sb0-4-31-2 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx0-4321 ∷ Toff123 ∷ Sb0-4-1-2 ∷ Toff123 ∷ Sb⁻0-4-1-2 ∷ []) (refl) ▸
       at 0 2 (Bx0-4312 ∷ Sw12 ∷ []) (lem-comm-push-BOX⟨0·4321⟩-sw1-R c4) ▸
       at 1 2 (Toff213 ∷ Sw12 ∷ []) (wl0127 c4) ▸
       at 2 2 (Sb0-4-2-1 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·4·1·2⟩-sw1-R c4) ▸
       at 3 2 (Toff213 ∷ Sw12 ∷ []) (wl0127 c4) ▸
       at 4 2 (Sb⁻0-4-2-1 ∷ Sw12 ∷ []) (lem-comm-push-SBOXd⟨0·4·1·2⟩-sw1-R c4) ▸
       at 0 5 (Sb0-4-31-2 ∷ []) (refl) ▸ done

-- comm push BOX(0;4312) sw2 R: 12 steps
lem-comm-push-BOX⟨0·4312⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Bx0-4312 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4213 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·4312⟩-sw2-R c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw23 ∷ Bx0-4312 ∷ []) (CCZ024 ∷ Toff024 ∷ Bx4-013 ∷ Toff024 ∷ Sw23 ∷ CCZ034 ∷ Bx4-012 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff034 ∷ Bx4-012 ∷ Toff034 ∷ CCZ034 ∷ Bx4-012 ∷ []) (refl) ▸
       at 1 1 (Sw23 ∷ CCZ024 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0003 c4) ▸
       at 2 1 (Sw23 ∷ Toff024 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0003 c4) ▸
       at 2 2 (Bx4-013 ∷ Sw23 ∷ []) (lem-comm-push-BOX⟨4·012⟩-sw2-R c4) ▸
       at 4 1 (Sw23 ∷ Toff024 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0003 c4) ▸ done

  b1 : Chain (CCZ024 ∷ Toff024 ∷ Bx4-013 ∷ Toff024 ∷ Sw23 ∷ CCZ034 ∷ Bx4-012 ∷ []) (Bx0-4213 ∷ Sw23 ∷ [])
  b1 = at 5 1 (Sw23 ∷ CCZ024 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0003 c4) ▸
       at 5 2 (Bx4-013 ∷ Sw23 ∷ []) (lem-comm-push-BOX⟨4·012⟩-sw2-R c4) ▸
       at 0 6 (Bx0-4213 ∷ []) (refl) ▸ done

-- comm push BOX(0;4213) sw0 R: 8 steps
lem-comm-push-BOX⟨0·4213⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Bx0-4213 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-4203 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·4213⟩-sw0-R c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-4213 ∷ []) (Bx1-4203 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx4-013 ∷ Toff024 ∷ CCZ024 ∷ Bx4-013 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw01 ∷ []) (lem-comm-push-CCZ024-sw0-R c4) ▸
       at 1 2 (Toff124 ∷ Sw01 ∷ []) (lem-comm-push-TOFF024-sw0-R c4) ▸
       at 2 2 (Bx4-103 ∷ Sw01 ∷ []) (lem-comm-push-BOX⟨4·013⟩-sw0-R c4) ▸
       at 3 2 (Toff124 ∷ Sw01 ∷ []) (lem-comm-push-TOFF024-sw0-R c4) ▸
       at 4 2 (CCZ124 ∷ Sw01 ∷ []) (lem-comm-push-CCZ024-sw0-R c4) ▸
       at 5 2 (Bx4-103 ∷ Sw01 ∷ []) (lem-comm-push-BOX⟨4·013⟩-sw0-R c4) ▸
       at 0 6 (Bx1-4203 ∷ []) (refl) ▸ done

-- comm push BOX(2;4103) sw0 R: 8 steps
lem-comm-push-BOX⟨2·4103⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Bx2-4103 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨2·4103⟩-sw0-R c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-4103 ∷ []) (Bx2-4013 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff214 ∷ Bx4-203 ∷ Toff214 ∷ CCZ124 ∷ Bx4-203 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw01 ∷ []) (lem-comm-push-CCZ124-sw0-R c4) ▸
       at 1 2 (Toff204 ∷ Sw01 ∷ []) (lem-comm-push-TOFF214-sw0-R c4) ▸
       at 2 2 (Bx4-213 ∷ Sw01 ∷ []) (lem-comm-push-BOX⟨4·203⟩-sw0-R c4) ▸
       at 3 2 (Toff204 ∷ Sw01 ∷ []) (lem-comm-push-TOFF214-sw0-R c4) ▸
       at 4 2 (CCZ024 ∷ Sw01 ∷ []) (lem-comm-push-CCZ124-sw0-R c4) ▸
       at 5 2 (Bx4-213 ∷ Sw01 ∷ []) (lem-comm-push-BOX⟨4·203⟩-sw0-R c4) ▸
       at 0 6 (Bx2-4013 ∷ []) (refl) ▸ done

-- comm push SBOX(0;2;43;1) sw0 R: 7 steps
lem-comm-push-SBOX⟨0·2·43·1⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-43-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨0·2·43·1⟩-sw0-R c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb0-2-43-1 ∷ []) (Sb1-2-43-0 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 0 2 (Bx1-2430 ∷ Sw01 ∷ []) (lem-comm-push-BOX⟨0·2431⟩-sw0-R c4) ▸
       at 1 2 (Toff034 ∷ Sw01 ∷ []) (lem-comm-push-TOFF134-sw0-R c4) ▸
       at 2 2 (Sb1-2-0-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·2·1·3⟩-sw0-R c4) ▸
       at 3 2 (Toff034 ∷ Sw01 ∷ []) (lem-comm-push-TOFF134-sw0-R c4) ▸
       at 4 2 (Sb⁻1-2-0-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOXd⟨0·2·1·3⟩-sw0-R c4) ▸
       at 0 5 (Sb1-2-43-0 ∷ []) (refl) ▸ done

-- comm push SBOX(1;2;43;0) sw1 R: 7 steps
lem-comm-push-SBOX⟨1·2·43·0⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Sb1-2-43-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-43-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨1·2·43·0⟩-sw1-R c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb1-2-43-0 ∷ []) (Sb2-1-43-0 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx1-2430 ∷ Toff034 ∷ Sb1-2-0-3 ∷ Toff034 ∷ Sb⁻1-2-0-3 ∷ []) (refl) ▸
       at 0 2 (Bx2-1430 ∷ Sw12 ∷ []) (lem-comm-push-BOX⟨1·2430⟩-sw1-R c4) ▸
       at 1 2 (Toff034 ∷ Sw12 ∷ []) (lem-comm-push-TOFF034-sw1-R c4) ▸
       at 2 2 (Sb2-1-0-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·2·0·3⟩-sw1-R c4) ▸
       at 3 2 (Toff034 ∷ Sw12 ∷ []) (lem-comm-push-TOFF034-sw1-R c4) ▸
       at 4 2 (Sb⁻2-1-0-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOXd⟨1·2·0·3⟩-sw1-R c4) ▸
       at 0 5 (Sb2-1-43-0 ∷ []) (refl) ▸ done

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

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R011 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL ; wl0004 ; wl0121 ; wl0063 ; wl0126)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-push-SBOXd⟨0·3·1·2⟩-sw3-R ; lem-comm-push-SBOXd⟨0·4·1·2⟩-sw3-L ; lem-comm-push-SBOXd⟨0·4·2·1⟩-sw2-R ; lem-comm-push-SBOXd⟨0·4·3·1⟩-sw2-L ; lem-comm-push-SBOXd⟨4·0·2·1⟩-sw2-R ; lem-comm-push-SBOXd⟨4·0·3·2⟩-sw0-R ; lem-comm-push-SBOX⟨0·3·1·2⟩-sw3-R ; lem-comm-push-SBOX⟨0·4·1·2⟩-sw3-L ; lem-comm-push-SBOX⟨0·4·2·1⟩-sw2-R ; lem-comm-push-SBOX⟨0·4·3·1⟩-sw2-L ; lem-comm-push-SBOX⟨4·0·2·1⟩-sw2-R ; lem-comm-push-SBOX⟨4·0·3·2⟩-sw0-R)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-comm-push-BOX⟨0·3421⟩-sw3-R ; lem-comm-push-BOX⟨0·4213⟩-sw0-R ; lem-comm-push-BOX⟨0·4213⟩-sw2-L ; lem-comm-push-BOX⟨0·4312⟩-sw2-R ; lem-comm-push-BOX⟨0·4321⟩-sw3-L ; lem-comm-push-BOX⟨1·4203⟩-sw0-L ; lem-comm-push-BOX⟨2·4013⟩-sw0-L ; lem-comm-push-BOX⟨2·4103⟩-sw0-R ; lem-comm-push-BOX⟨4·0123⟩-sw0-R ; lem-comm-push-BOX⟨4·0312⟩-sw2-R)

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

-- comm push SBOX(0;4;31;2) sw2 R: 7 steps
lem-comm-push-SBOX⟨0·4·31·2⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Sb0-4-31-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-4-21-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨0·4·31·2⟩-sw2-R c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb0-4-31-2 ∷ []) (Sb0-4-21-3 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx0-4312 ∷ Toff213 ∷ Sb0-4-2-1 ∷ Toff213 ∷ Sb⁻0-4-2-1 ∷ []) (refl) ▸
       at 0 2 (Bx0-4213 ∷ Sw23 ∷ []) (lem-comm-push-BOX⟨0·4312⟩-sw2-R c4) ▸
       at 1 2 (Toff312 ∷ Sw23 ∷ []) (wl0126 c4) ▸
       at 2 2 (Sb0-4-3-1 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·4·2·1⟩-sw2-R c4) ▸
       at 3 2 (Toff312 ∷ Sw23 ∷ []) (wl0126 c4) ▸
       at 4 2 (Sb⁻0-4-3-1 ∷ Sw23 ∷ []) (lem-comm-push-SBOXd⟨0·4·2·1⟩-sw2-R c4) ▸
       at 0 5 (Sb0-4-21-3 ∷ []) (refl) ▸ done

-- comm push SBOX(0;4;21;3) sw0 R: 7 steps
lem-comm-push-SBOX⟨0·4·21·3⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Sb0-4-21-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-4-20-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨0·4·21·3⟩-sw0-R c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb0-4-21-3 ∷ []) (Sb1-4-20-3 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx0-4213 ∷ Toff312 ∷ Sb0-4-3-1 ∷ Toff312 ∷ Sb⁻0-4-3-1 ∷ []) (refl) ▸
       at 0 2 (Bx1-4203 ∷ Sw01 ∷ []) (lem-comm-push-BOX⟨0·4213⟩-sw0-R c4) ▸
       at 1 2 (Toff302 ∷ Sw01 ∷ []) (wl0063 c4) ▸
       at 2 2 (Sb0-4-3-1 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑)) ▸
       at 3 2 (Toff302 ∷ Sw01 ∷ []) (wl0063 c4) ▸
       at 4 2 (Sb⁻0-4-3-1 ∷ Sw01 ∷ []) (c₂ (Swap) ((CS • CS • CS) ↑)) ▸
       at 0 5 (Sb1-4-20-3 ∷ []) (refl) ▸ done

-- comm push SBOX(2;4;10;3) sw0 R: 7 steps
lem-comm-push-SBOX⟨2·4·10·3⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Sb2-4-10-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-01-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨2·4·10·3⟩-sw0-R c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb2-4-10-3 ∷ []) (Sb2-4-01-3 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx2-4103 ∷ Toff301 ∷ Sb2-4-3-0 ∷ Toff301 ∷ Sb⁻2-4-3-0 ∷ []) (refl) ▸
       at 0 2 (Bx2-4013 ∷ Sw01 ∷ []) (lem-comm-push-BOX⟨2·4103⟩-sw0-R c4) ▸
       at 1 2 (Toff301 ∷ Sw01 ∷ []) (wl0121 c4) ▸
       at 2 2 (Sb2-4-3-0 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑)) ▸
       at 3 2 (Toff301 ∷ Sw01 ∷ []) (wl0121 c4) ▸
       at 4 2 (Sb⁻2-4-3-0 ∷ Sw01 ∷ []) (c₂ (Swap) ((CS • CS • CS) ↑)) ▸
       at 0 5 (Sb2-4-01-3 ∷ []) (refl) ▸ done

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

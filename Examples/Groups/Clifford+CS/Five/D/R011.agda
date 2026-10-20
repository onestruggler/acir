{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R011 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL ; wl0004 ; wl0121 ; wl0063 ; wl0126)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-push-SBOXd⟨0·3·1·2⟩-sw3-R ; lem-comm-push-SBOXd⟨0·4·1·2⟩-sw3-L ; lem-comm-push-SBOXd⟨0·4·2·1⟩-sw2-R ; lem-comm-push-SBOXd⟨0·4·3·1⟩-sw2-L ; lem-comm-push-SBOXd⟨4·0·2·1⟩-sw2-R ; lem-comm-push-SBOXd⟨4·0·3·2⟩-sw0-R ; lem-comm-push-SBOX⟨0·3·1·2⟩-sw3-R ; lem-comm-push-SBOX⟨0·4·1·2⟩-sw3-L ; lem-comm-push-SBOX⟨0·4·2·1⟩-sw2-R ; lem-comm-push-SBOX⟨0·4·3·1⟩-sw2-L ; lem-comm-push-SBOX⟨4·0·2·1⟩-sw2-R ; lem-comm-push-SBOX⟨4·0·3·2⟩-sw0-R)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-comm-push-BOX⟨0·3421⟩-sw3-R ; lem-comm-push-BOX⟨0·4213⟩-sw0-R ; lem-comm-push-BOX⟨0·4213⟩-sw2-L ; lem-comm-push-BOX⟨0·4312⟩-sw2-R ; lem-comm-push-BOX⟨0·4321⟩-sw3-L ; lem-comm-push-BOX⟨1·4203⟩-sw0-L ; lem-comm-push-BOX⟨2·4013⟩-sw0-L ; lem-comm-push-BOX⟨2·4103⟩-sw0-R ; lem-comm-push-BOX⟨4·0123⟩-sw0-R ; lem-comm-push-BOX⟨4·0312⟩-sw2-R)

private
  q1 : WsL → Eqn
  q1 c4 = eqn (Sw01 ∷ Sb⁻2-4-3-1 ∷ []) (Sb⁻2-4-3-1 ∷ Sw01 ∷ []) (c₂ (Swap) ((CS • CS • CS) ↑))
  q2 : WsL → Eqn
  q2 c4 = eqn (Sw01 ∷ Toff301 ∷ []) (Toff301 ∷ Sw01 ∷ []) (wl0121 c4)
  q3 : WsL → Eqn
  q3 c4 = eqn (Sw01 ∷ Sb2-4-3-1 ∷ []) (Sb2-4-3-1 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑))
  q4 : WsL → Eqn
  q4 c4 = eqn (Bx2-4013 ∷ Sw01 ∷ []) (Sw01 ∷ Bx2-4103 ∷ []) (lem-comm-push-BOX⟨2·4013⟩-sw0-L c4)

-- comm push SBOX(2;4;01;3) sw0 L: 7 steps
lem-comm-push-SBOX⟨2·4·01·3⟩-sw0-L : WsL → ⟪ (Sb2-4-01-3 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Sb2-4-10-3 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨2·4·01·3⟩-sw0-L c4 = derive (Sb2-4-01-3 ∷ Sw01 ∷ []) (Sw01 ∷ Sb2-4-10-3 ∷ [])
  (re 0 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) ∷
   rw⁻ 4 (q1 c4) ∷
   rw⁻ 3 (q2 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   rw⁻ 1 (q2 c4) ∷
   rw 0 (q4 c4) ∷
   re 1 5 (Sb2-4-10-3 ∷ []) ∷ []) Eq.refl

private
  q5 : WsL → Eqn
  q5 c4 = eqn (Sw01 ∷ Sb⁻1-4-3-0 ∷ []) (Sb⁻1-4-3-0 ∷ Sw01 ∷ []) (c₂ (Swap) ((CS • CS • CS) ↑))
  q6 : WsL → Eqn
  q6 c4 = eqn (Sw01 ∷ Toff312 ∷ []) (Toff302 ∷ Sw01 ∷ []) (wl0063 c4)
  q7 : WsL → Eqn
  q7 c4 = eqn (Sw01 ∷ Sb1-4-3-0 ∷ []) (Sb1-4-3-0 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑))
  q8 : WsL → Eqn
  q8 c4 = eqn (Bx1-4203 ∷ Sw01 ∷ []) (Sw01 ∷ Bx0-4213 ∷ []) (lem-comm-push-BOX⟨1·4203⟩-sw0-L c4)

-- comm push SBOX(1;4;20;3) sw0 L: 7 steps
lem-comm-push-SBOX⟨1·4·20·3⟩-sw0-L : WsL → ⟪ (Sb1-4-20-3 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Sb0-4-21-3 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨1·4·20·3⟩-sw0-L c4 = derive (Sb1-4-20-3 ∷ Sw01 ∷ []) (Sw01 ∷ Sb0-4-21-3 ∷ [])
  (re 0 1 (Bx1-4203 ∷ Toff302 ∷ Sb1-4-3-0 ∷ Toff302 ∷ Sb⁻1-4-3-0 ∷ []) ∷
   rw⁻ 4 (q5 c4) ∷
   rw⁻ 3 (q6 c4) ∷
   rw⁻ 2 (q7 c4) ∷
   rw⁻ 1 (q6 c4) ∷
   rw 0 (q8 c4) ∷
   re 1 5 (Sb0-4-21-3 ∷ []) ∷ []) Eq.refl

private
  q9 : WsL → Eqn
  q9 c4 = eqn (Sb⁻0-4-3-1 ∷ Sw23 ∷ []) (Sw23 ∷ Sb⁻0-4-2-1 ∷ []) (lem-comm-push-SBOXd⟨0·4·3·1⟩-sw2-L c4)
  q10 : WsL → Eqn
  q10 c4 = eqn (Sw23 ∷ Toff213 ∷ []) (Toff312 ∷ Sw23 ∷ []) (wl0126 c4)
  q11 : WsL → Eqn
  q11 c4 = eqn (Sb0-4-3-1 ∷ Sw23 ∷ []) (Sw23 ∷ Sb0-4-2-1 ∷ []) (lem-comm-push-SBOX⟨0·4·3·1⟩-sw2-L c4)
  q12 : WsL → Eqn
  q12 c4 = eqn (Bx0-4213 ∷ Sw23 ∷ []) (Sw23 ∷ Bx0-4312 ∷ []) (lem-comm-push-BOX⟨0·4213⟩-sw2-L c4)

-- comm push SBOX(0;4;21;3) sw2 L: 7 steps
lem-comm-push-SBOX⟨0·4·21·3⟩-sw2-L : WsL → ⟪ (Sb0-4-21-3 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sb0-4-31-2 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨0·4·21·3⟩-sw2-L c4 = derive (Sb0-4-21-3 ∷ Sw23 ∷ []) (Sw23 ∷ Sb0-4-31-2 ∷ [])
  (re 0 1 (Bx0-4213 ∷ Toff312 ∷ Sb0-4-3-1 ∷ Toff312 ∷ Sb⁻0-4-3-1 ∷ []) ∷
   rw 4 (q9 c4) ∷
   rw⁻ 3 (q10 c4) ∷
   rw 2 (q11 c4) ∷
   rw⁻ 1 (q10 c4) ∷
   rw 0 (q12 c4) ∷
   re 1 5 (Sb0-4-31-2 ∷ []) ∷ []) Eq.refl

private
  q13 : WsL → Eqn
  q13 c4 = eqn (Sb⁻0-4-1-2 ∷ Sw34 ∷ []) (Sw34 ∷ Sb⁻0-3-1-2 ∷ []) (lem-comm-push-SBOXd⟨0·4·1·2⟩-sw3-L c4)
  q14 : WsL → Eqn
  q14 c4 = eqn (Sw34 ∷ Sw34 ∷ []) [] (wl0004 c4)
  q15 : WsL → Eqn
  q15 c4 = eqn (Sb0-4-1-2 ∷ Sw34 ∷ []) (Sw34 ∷ Sb0-3-1-2 ∷ []) (lem-comm-push-SBOX⟨0·4·1·2⟩-sw3-L c4)
  q16 : WsL → Eqn
  q16 c4 = eqn (Bx0-4321 ∷ Sw34 ∷ []) (Sw34 ∷ Bx0-3421 ∷ []) (lem-comm-push-BOX⟨0·4321⟩-sw3-L c4)

-- comm push SBOX(0;4;32;1) sw3 L: 9 steps
lem-comm-push-SBOX⟨0·4·32·1⟩-sw3-L : WsL → ⟪ (Sb0-4-32-1 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Sw34 ∷ Sb0-3-42-1 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨0·4·32·1⟩-sw3-L c4 = derive (Sb0-4-32-1 ∷ Sw34 ∷ []) (Sw34 ∷ Sb0-3-42-1 ∷ [])
  (re 0 1 (Bx0-4321 ∷ Toff123 ∷ Sb0-4-1-2 ∷ Toff123 ∷ Sb⁻0-4-1-2 ∷ []) ∷
   rw 4 (q13 c4) ∷
   rw⁻ 3 (q14 c4) ∷
   re 4 3 (Toff124 ∷ []) ∷
   rw 2 (q15 c4) ∷
   rw⁻ 1 (q14 c4) ∷
   re 2 3 (Toff124 ∷ []) ∷
   rw 0 (q16 c4) ∷
   re 1 5 (Sb0-3-42-1 ∷ []) ∷ []) Eq.refl

private
  q17 : WsL → Eqn
  q17 c4 = eqn (Sw34 ∷ Bx0-3421 ∷ []) (Bx0-4321 ∷ Sw34 ∷ []) (lem-comm-push-BOX⟨0·3421⟩-sw3-R c4)
  q18 : WsL → Eqn
  q18 c4 = eqn (Sw34 ∷ Sb0-3-1-2 ∷ []) (Sb0-4-1-2 ∷ Sw34 ∷ []) (lem-comm-push-SBOX⟨0·3·1·2⟩-sw3-R c4)
  q19 : WsL → Eqn
  q19 c4 = eqn (Sw34 ∷ Sb⁻0-3-1-2 ∷ []) (Sb⁻0-4-1-2 ∷ Sw34 ∷ []) (lem-comm-push-SBOXd⟨0·3·1·2⟩-sw3-R c4)

-- comm push SBOX(0;3;42;1) sw3 R: 9 steps
lem-comm-push-SBOX⟨0·3·42·1⟩-sw3-R : WsL → ⟪ (Sw34 ∷ Sb0-3-42-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-4-32-1 ∷ Sw34 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨0·3·42·1⟩-sw3-R c4 = derive (Sw34 ∷ Sb0-3-42-1 ∷ []) (Sb0-4-32-1 ∷ Sw34 ∷ [])
  (re 1 1 (Bx0-3421 ∷ Toff124 ∷ Sb0-3-1-2 ∷ Toff124 ∷ Sb⁻0-3-1-2 ∷ []) ∷
   rw 0 (q17 c4) ∷
   re 2 1 (Sw34 ∷ Toff123 ∷ Sw34 ∷ []) ∷
   rw 1 (q14 c4) ∷
   rw 2 (q18 c4) ∷
   re 4 1 (Sw34 ∷ Toff123 ∷ Sw34 ∷ []) ∷
   rw 3 (q14 c4) ∷
   rw 4 (q19 c4) ∷
   re 0 5 (Sb0-4-32-1 ∷ []) ∷ []) Eq.refl

private
  q20 : WsL → Eqn
  q20 c4 = eqn (Sw23 ∷ Bx0-4312 ∷ []) (Bx0-4213 ∷ Sw23 ∷ []) (lem-comm-push-BOX⟨0·4312⟩-sw2-R c4)
  q21 : WsL → Eqn
  q21 c4 = eqn (Sw23 ∷ Sb0-4-2-1 ∷ []) (Sb0-4-3-1 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·4·2·1⟩-sw2-R c4)
  q22 : WsL → Eqn
  q22 c4 = eqn (Sw23 ∷ Sb⁻0-4-2-1 ∷ []) (Sb⁻0-4-3-1 ∷ Sw23 ∷ []) (lem-comm-push-SBOXd⟨0·4·2·1⟩-sw2-R c4)

-- comm push SBOX(0;4;31;2) sw2 R: 7 steps
lem-comm-push-SBOX⟨0·4·31·2⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Sb0-4-31-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-4-21-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨0·4·31·2⟩-sw2-R c4 = derive (Sw23 ∷ Sb0-4-31-2 ∷ []) (Sb0-4-21-3 ∷ Sw23 ∷ [])
  (re 1 1 (Bx0-4312 ∷ Toff213 ∷ Sb0-4-2-1 ∷ Toff213 ∷ Sb⁻0-4-2-1 ∷ []) ∷
   rw 0 (q20 c4) ∷
   rw 1 (q10 c4) ∷
   rw 2 (q21 c4) ∷
   rw 3 (q10 c4) ∷
   rw 4 (q22 c4) ∷
   re 0 5 (Sb0-4-21-3 ∷ []) ∷ []) Eq.refl

private
  q23 : WsL → Eqn
  q23 c4 = eqn (Sw01 ∷ Bx0-4213 ∷ []) (Bx1-4203 ∷ Sw01 ∷ []) (lem-comm-push-BOX⟨0·4213⟩-sw0-R c4)
  q24 : WsL → Eqn
  q24 c4 = eqn (Sw01 ∷ Sb0-4-3-1 ∷ []) (Sb0-4-3-1 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑))
  q25 : WsL → Eqn
  q25 c4 = eqn (Sw01 ∷ Sb⁻0-4-3-1 ∷ []) (Sb⁻0-4-3-1 ∷ Sw01 ∷ []) (c₂ (Swap) ((CS • CS • CS) ↑))

-- comm push SBOX(0;4;21;3) sw0 R: 7 steps
lem-comm-push-SBOX⟨0·4·21·3⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Sb0-4-21-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-4-20-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨0·4·21·3⟩-sw0-R c4 = derive (Sw01 ∷ Sb0-4-21-3 ∷ []) (Sb1-4-20-3 ∷ Sw01 ∷ [])
  (re 1 1 (Bx0-4213 ∷ Toff312 ∷ Sb0-4-3-1 ∷ Toff312 ∷ Sb⁻0-4-3-1 ∷ []) ∷
   rw 0 (q23 c4) ∷
   rw 1 (q6 c4) ∷
   rw 2 (q24 c4) ∷
   rw 3 (q6 c4) ∷
   rw 4 (q25 c4) ∷
   re 0 5 (Sb1-4-20-3 ∷ []) ∷ []) Eq.refl

private
  q26 : WsL → Eqn
  q26 c4 = eqn (Sw01 ∷ Bx2-4103 ∷ []) (Bx2-4013 ∷ Sw01 ∷ []) (lem-comm-push-BOX⟨2·4103⟩-sw0-R c4)
  q27 : WsL → Eqn
  q27 c4 = eqn (Sw01 ∷ Sb2-4-3-0 ∷ []) (Sb2-4-3-0 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑))
  q28 : WsL → Eqn
  q28 c4 = eqn (Sw01 ∷ Sb⁻2-4-3-0 ∷ []) (Sb⁻2-4-3-0 ∷ Sw01 ∷ []) (c₂ (Swap) ((CS • CS • CS) ↑))

-- comm push SBOX(2;4;10;3) sw0 R: 7 steps
lem-comm-push-SBOX⟨2·4·10·3⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Sb2-4-10-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-01-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨2·4·10·3⟩-sw0-R c4 = derive (Sw01 ∷ Sb2-4-10-3 ∷ []) (Sb2-4-01-3 ∷ Sw01 ∷ [])
  (re 1 1 (Bx2-4103 ∷ Toff301 ∷ Sb2-4-3-0 ∷ Toff301 ∷ Sb⁻2-4-3-0 ∷ []) ∷
   rw 0 (q26 c4) ∷
   rw 1 (q2 c4) ∷
   rw 2 (q27 c4) ∷
   rw 3 (q2 c4) ∷
   rw 4 (q28 c4) ∷
   re 0 5 (Sb2-4-01-3 ∷ []) ∷ []) Eq.refl

private
  q29 : WsL → Eqn
  q29 c4 = eqn (Sw23 ∷ Bx4-0312 ∷ []) (Bx4-0213 ∷ Sw23 ∷ []) (lem-comm-push-BOX⟨4·0312⟩-sw2-R c4)
  q30 : WsL → Eqn
  q30 c4 = eqn (Sw23 ∷ Sb4-0-2-1 ∷ []) (Sb4-0-3-1 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨4·0·2·1⟩-sw2-R c4)
  q31 : WsL → Eqn
  q31 c4 = eqn (Sw23 ∷ Sb⁻4-0-2-1 ∷ []) (Sb⁻4-0-3-1 ∷ Sw23 ∷ []) (lem-comm-push-SBOXd⟨4·0·2·1⟩-sw2-R c4)

-- comm push SBOX(4;0;31;2) sw2 R: 7 steps
lem-comm-push-SBOX⟨4·0·31·2⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Sb4-0-31-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-0-21-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨4·0·31·2⟩-sw2-R c4 = derive (Sw23 ∷ Sb4-0-31-2 ∷ []) (Sb4-0-21-3 ∷ Sw23 ∷ [])
  (re 1 1 (Bx4-0312 ∷ Toff213 ∷ Sb4-0-2-1 ∷ Toff213 ∷ Sb⁻4-0-2-1 ∷ []) ∷
   rw 0 (q29 c4) ∷
   rw 1 (q10 c4) ∷
   rw 2 (q30 c4) ∷
   rw 3 (q10 c4) ∷
   rw 4 (q31 c4) ∷
   re 0 5 (Sb4-0-21-3 ∷ []) ∷ []) Eq.refl

private
  q32 : WsL → Eqn
  q32 c4 = eqn (Sw01 ∷ Bx4-0123 ∷ []) (Bx4-1023 ∷ Sw01 ∷ []) (lem-comm-push-BOX⟨4·0123⟩-sw0-R c4)
  q33 : WsL → Eqn
  q33 c4 = eqn (Sw01 ∷ Sb4-0-3-2 ∷ []) (Sb4-1-3-2 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨4·0·3·2⟩-sw0-R c4)
  q34 : WsL → Eqn
  q34 c4 = eqn (Sw01 ∷ Sb⁻4-0-3-2 ∷ []) (Sb⁻4-1-3-2 ∷ Sw01 ∷ []) (lem-comm-push-SBOXd⟨4·0·3·2⟩-sw0-R c4)

-- comm push SBOX(4;0;12;3) sw0 R: 7 steps
lem-comm-push-SBOX⟨4·0·12·3⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Sb4-0-12-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-1-02-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨4·0·12·3⟩-sw0-R c4 = derive (Sw01 ∷ Sb4-0-12-3 ∷ []) (Sb4-1-02-3 ∷ Sw01 ∷ [])
  (re 1 1 (Bx4-0123 ∷ Toff312 ∷ Sb4-0-3-2 ∷ Toff312 ∷ Sb⁻4-0-3-2 ∷ []) ∷
   rw 0 (q32 c4) ∷
   rw 1 (q6 c4) ∷
   rw 2 (q33 c4) ∷
   rw 3 (q6 c4) ∷
   rw 4 (q34 c4) ∷
   re 0 5 (Sb4-1-02-3 ∷ []) ∷ []) Eq.refl

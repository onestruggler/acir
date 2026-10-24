{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SR011 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.R011 (Sᴰ : SR011) where

open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.Str using (ℓ)

-- The lemmas of other derivation modules (DSig).
private
  lem-comm-push-SBOXd⟨0·3·1·2⟩-sw3-R : WsL → St 2543
  lem-comm-push-SBOXd⟨0·3·1·2⟩-sw3-R = pickᴰ 0 Sᴰ
  lem-comm-push-SBOXd⟨0·4·1·2⟩-sw3-L : WsL → St 2544
  lem-comm-push-SBOXd⟨0·4·1·2⟩-sw3-L = pickᴰ 1 Sᴰ
  lem-comm-push-SBOXd⟨0·4·2·1⟩-sw2-R : WsL → St 2545
  lem-comm-push-SBOXd⟨0·4·2·1⟩-sw2-R = pickᴰ 2 Sᴰ
  lem-comm-push-SBOXd⟨0·4·3·1⟩-sw2-L : WsL → St 2546
  lem-comm-push-SBOXd⟨0·4·3·1⟩-sw2-L = pickᴰ 3 Sᴰ
  lem-comm-push-SBOXd⟨4·0·2·1⟩-sw2-R : WsL → St 2547
  lem-comm-push-SBOXd⟨4·0·2·1⟩-sw2-R = pickᴰ 4 Sᴰ
  lem-comm-push-SBOXd⟨4·0·3·2⟩-sw0-R : WsL → St 2548
  lem-comm-push-SBOXd⟨4·0·3·2⟩-sw0-R = pickᴰ 5 Sᴰ
  lem-comm-push-SBOX⟨0·3·1·2⟩-sw3-R : WsL → St 2549
  lem-comm-push-SBOX⟨0·3·1·2⟩-sw3-R = pickᴰ 6 Sᴰ
  lem-comm-push-SBOX⟨0·4·1·2⟩-sw3-L : WsL → St 2550
  lem-comm-push-SBOX⟨0·4·1·2⟩-sw3-L = pickᴰ 7 Sᴰ
  lem-comm-push-SBOX⟨0·4·2·1⟩-sw2-R : WsL → St 2551
  lem-comm-push-SBOX⟨0·4·2·1⟩-sw2-R = pickᴰ 8 Sᴰ
  lem-comm-push-SBOX⟨0·4·3·1⟩-sw2-L : WsL → St 2552
  lem-comm-push-SBOX⟨0·4·3·1⟩-sw2-L = pickᴰ 9 Sᴰ
  lem-comm-push-SBOX⟨4·0·2·1⟩-sw2-R : WsL → St 2553
  lem-comm-push-SBOX⟨4·0·2·1⟩-sw2-R = pickᴰ 10 Sᴰ
  lem-comm-push-SBOX⟨4·0·3·2⟩-sw0-R : WsL → St 2554
  lem-comm-push-SBOX⟨4·0·3·2⟩-sw0-R = pickᴰ 11 Sᴰ
  lem-comm-push-BOX⟨0·3421⟩-sw3-R : WsL → St 2555
  lem-comm-push-BOX⟨0·3421⟩-sw3-R = pickᴰ 12 Sᴰ
  lem-comm-push-BOX⟨0·4213⟩-sw0-R : WsL → St 2556
  lem-comm-push-BOX⟨0·4213⟩-sw0-R = pickᴰ 13 Sᴰ
  lem-comm-push-BOX⟨0·4213⟩-sw2-L : WsL → St 2557
  lem-comm-push-BOX⟨0·4213⟩-sw2-L = pickᴰ 14 Sᴰ
  lem-comm-push-BOX⟨0·4312⟩-sw2-R : WsL → St 2558
  lem-comm-push-BOX⟨0·4312⟩-sw2-R = pickᴰ 15 Sᴰ
  lem-comm-push-BOX⟨0·4321⟩-sw3-L : WsL → St 2559
  lem-comm-push-BOX⟨0·4321⟩-sw3-L = pickᴰ 16 Sᴰ
  lem-comm-push-BOX⟨1·4203⟩-sw0-L : WsL → St 2560
  lem-comm-push-BOX⟨1·4203⟩-sw0-L = pickᴰ 17 Sᴰ
  lem-comm-push-BOX⟨2·4013⟩-sw0-L : WsL → St 2561
  lem-comm-push-BOX⟨2·4013⟩-sw0-L = pickᴰ 18 Sᴰ
  lem-comm-push-BOX⟨2·4103⟩-sw0-R : WsL → St 2562
  lem-comm-push-BOX⟨2·4103⟩-sw0-R = pickᴰ 19 Sᴰ
  lem-comm-push-BOX⟨4·0123⟩-sw0-R : WsL → St 2563
  lem-comm-push-BOX⟨4·0123⟩-sw0-R = pickᴰ 20 Sᴰ
  lem-comm-push-BOX⟨4·0312⟩-sw2-R : WsL → St 2564
  lem-comm-push-BOX⟨4·0312⟩-sw2-R = pickᴰ 21 Sᴰ

private
  q1 : WsL → Eqn
  q1 c4 = eqn (ℓ "丫俉") (ℓ "俉丫") (c₂ (Swap) ((CS • CS • CS) ↑))
  q2 : WsL → Eqn
  q2 c4 = wlE 121 c4
  q3 : WsL → Eqn
  q3 c4 = eqn (ℓ "丫俈") (ℓ "俈丫") (c₂ (Swap) (CS ↑))
  q4 : WsL → Eqn
  q4 c4 = sE 2561 (lem-comm-push-BOX⟨2·4013⟩-sw0-L c4)

-- comm push SBOX(2;4;01;3) sw0 L: 7 steps
lem-comm-push-SBOX⟨2·4·01·3⟩-sw0-L : WsL → ⟪ (ℓ "俊丫") ⟫ʷ ≈ ⟪ (ℓ "丫俍") ⟫ʷ
lem-comm-push-SBOX⟨2·4·01·3⟩-sw0-L c4 = derive (ℓ "俊丫") (ℓ "丫俍")
  (re 0 1 (ℓ "佔亓俈亓俉") ∷
   rw⁻ 4 (q1 c4) ∷
   rw⁻ 3 (q2 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   rw⁻ 1 (q2 c4) ∷
   rw 0 (q4 c4) ∷
   re 1 5 (ℓ "俍") ∷ []) Eq.refl

private
  q5 : WsL → Eqn
  q5 c4 = eqn (ℓ "丫俀") (ℓ "俀丫") (c₂ (Swap) ((CS • CS • CS) ↑))
  q6 : WsL → Eqn
  q6 c4 = wlE 63 c4
  q7 : WsL → Eqn
  q7 c4 = eqn (ℓ "丫便") (ℓ "便丫") (c₂ (Swap) (CS ↑))
  q8 : WsL → Eqn
  q8 c4 = sE 2560 (lem-comm-push-BOX⟨1·4203⟩-sw0-L c4)

-- comm push SBOX(1;4;20;3) sw0 L: 7 steps
lem-comm-push-SBOX⟨1·4·20·3⟩-sw0-L : WsL → ⟪ (ℓ "俁丫") ⟫ʷ ≈ ⟪ (ℓ "丫侴") ⟫ʷ
lem-comm-push-SBOX⟨1·4·20·3⟩-sw0-L c4 = derive (ℓ "俁丫") (ℓ "丫侴")
  (re 0 1 (ℓ "伪些便些俀") ∷
   rw⁻ 4 (q5 c4) ∷
   rw⁻ 3 (q6 c4) ∷
   rw⁻ 2 (q7 c4) ∷
   rw⁻ 1 (q6 c4) ∷
   rw 0 (q8 c4) ∷
   re 1 5 (ℓ "侴") ∷ []) Eq.refl

private
  q9 : WsL → Eqn
  q9 c4 = sE 2546 (lem-comm-push-SBOXd⟨0·4·3·1⟩-sw2-L c4)
  q10 : WsL → Eqn
  q10 c4 = wlE 126 c4
  q11 : WsL → Eqn
  q11 c4 = sE 2552 (lem-comm-push-SBOX⟨0·4·3·1⟩-sw2-L c4)
  q12 : WsL → Eqn
  q12 c4 = sE 2557 (lem-comm-push-BOX⟨0·4213⟩-sw2-L c4)

-- comm push SBOX(0;4;21;3) sw2 L: 7 steps
lem-comm-push-SBOX⟨0·4·21·3⟩-sw2-L : WsL → ⟪ (ℓ "侴乥") ⟫ʷ ≈ ⟪ (ℓ "乥侶") ⟫ʷ
lem-comm-push-SBOX⟨0·4·21·3⟩-sw2-L c4 = derive (ℓ "侴乥") (ℓ "乥侶")
  (re 0 1 (ℓ "伅产侲产侳") ∷
   rw 4 (q9 c4) ∷
   rw⁻ 3 (q10 c4) ∷
   rw 2 (q11 c4) ∷
   rw⁻ 1 (q10 c4) ∷
   rw 0 (q12 c4) ∷
   re 1 5 (ℓ "侶") ∷ []) Eq.refl

private
  q13 : WsL → Eqn
  q13 c4 = sE 2544 (lem-comm-push-SBOXd⟨0·4·1·2⟩-sw3-L c4)
  q14 : WsL → Eqn
  q14 c4 = wlE 4 c4
  q15 : WsL → Eqn
  q15 c4 = sE 2550 (lem-comm-push-SBOX⟨0·4·1·2⟩-sw3-L c4)
  q16 : WsL → Eqn
  q16 c4 = sE 2559 (lem-comm-push-BOX⟨0·4321⟩-sw3-L c4)

-- comm push SBOX(0;4;32;1) sw3 L: 9 steps
lem-comm-push-SBOX⟨0·4·32·1⟩-sw3-L : WsL → ⟪ (ℓ "侸乼") ⟫ʷ ≈ ⟪ (ℓ "乼侯") ⟫ʷ
lem-comm-push-SBOX⟨0·4·32·1⟩-sw3-L c4 = derive (ℓ "侸乼") (ℓ "乼侯")
  (re 0 1 (ℓ "伍亥侰亥侷") ∷
   rw 4 (q13 c4) ∷
   rw⁻ 3 (q14 c4) ∷
   re 4 3 (ℓ "亩") ∷
   rw 2 (q15 c4) ∷
   rw⁻ 1 (q14 c4) ∷
   re 2 3 (ℓ "亩") ∷
   rw 0 (q16 c4) ∷
   re 1 5 (ℓ "侯") ∷ []) Eq.refl

private
  q17 : WsL → Eqn
  q17 c4 = sE 2555 (lem-comm-push-BOX⟨0·3421⟩-sw3-R c4)
  q18 : WsL → Eqn
  q18 c4 = sE 2549 (lem-comm-push-SBOX⟨0·3·1·2⟩-sw3-R c4)
  q19 : WsL → Eqn
  q19 c4 = sE 2543 (lem-comm-push-SBOXd⟨0·3·1·2⟩-sw3-R c4)

-- comm push SBOX(0;3;42;1) sw3 R: 9 steps
lem-comm-push-SBOX⟨0·3·42·1⟩-sw3-R : WsL → ⟪ (ℓ "乼侯") ⟫ʷ ≈ ⟪ (ℓ "侸乼") ⟫ʷ
lem-comm-push-SBOX⟨0·3·42·1⟩-sw3-R c4 = derive (ℓ "乼侯") (ℓ "侸乼")
  (re 1 1 (ℓ "件亩侭亩侮") ∷
   rw 0 (q17 c4) ∷
   re 2 1 (ℓ "乼亥乼") ∷
   rw 1 (q14 c4) ∷
   rw 2 (q18 c4) ∷
   re 4 1 (ℓ "乼亥乼") ∷
   rw 3 (q14 c4) ∷
   rw 4 (q19 c4) ∷
   re 0 5 (ℓ "侸") ∷ []) Eq.refl

private
  q20 : WsL → Eqn
  q20 c4 = sE 2558 (lem-comm-push-BOX⟨0·4312⟩-sw2-R c4)
  q21 : WsL → Eqn
  q21 c4 = sE 2551 (lem-comm-push-SBOX⟨0·4·2·1⟩-sw2-R c4)
  q22 : WsL → Eqn
  q22 c4 = sE 2545 (lem-comm-push-SBOXd⟨0·4·2·1⟩-sw2-R c4)

-- comm push SBOX(0;4;31;2) sw2 R: 7 steps
lem-comm-push-SBOX⟨0·4·31·2⟩-sw2-R : WsL → ⟪ (ℓ "乥侶") ⟫ʷ ≈ ⟪ (ℓ "侴乥") ⟫ʷ
lem-comm-push-SBOX⟨0·4·31·2⟩-sw2-R c4 = derive (ℓ "乥侶") (ℓ "侴乥")
  (re 1 1 (ℓ "伋亦侱亦侵") ∷
   rw 0 (q20 c4) ∷
   rw 1 (q10 c4) ∷
   rw 2 (q21 c4) ∷
   rw 3 (q10 c4) ∷
   rw 4 (q22 c4) ∷
   re 0 5 (ℓ "侴") ∷ []) Eq.refl

private
  q23 : WsL → Eqn
  q23 c4 = sE 2556 (lem-comm-push-BOX⟨0·4213⟩-sw0-R c4)
  q24 : WsL → Eqn
  q24 c4 = eqn (ℓ "丫侲") (ℓ "侲丫") (c₂ (Swap) (CS ↑))
  q25 : WsL → Eqn
  q25 c4 = eqn (ℓ "丫侳") (ℓ "侳丫") (c₂ (Swap) ((CS • CS • CS) ↑))

-- comm push SBOX(0;4;21;3) sw0 R: 7 steps
lem-comm-push-SBOX⟨0·4·21·3⟩-sw0-R : WsL → ⟪ (ℓ "丫侴") ⟫ʷ ≈ ⟪ (ℓ "俁丫") ⟫ʷ
lem-comm-push-SBOX⟨0·4·21·3⟩-sw0-R c4 = derive (ℓ "丫侴") (ℓ "俁丫")
  (re 1 1 (ℓ "伅产侲产侳") ∷
   rw 0 (q23 c4) ∷
   rw 1 (q6 c4) ∷
   rw 2 (q24 c4) ∷
   rw 3 (q6 c4) ∷
   rw 4 (q25 c4) ∷
   re 0 5 (ℓ "俁") ∷ []) Eq.refl

private
  q26 : WsL → Eqn
  q26 c4 = sE 2562 (lem-comm-push-BOX⟨2·4103⟩-sw0-R c4)
  q27 : WsL → Eqn
  q27 c4 = eqn (ℓ "丫俋") (ℓ "俋丫") (c₂ (Swap) (CS ↑))
  q28 : WsL → Eqn
  q28 c4 = eqn (ℓ "丫俌") (ℓ "俌丫") (c₂ (Swap) ((CS • CS • CS) ↑))

-- comm push SBOX(2;4;10;3) sw0 R: 7 steps
lem-comm-push-SBOX⟨2·4·10·3⟩-sw0-R : WsL → ⟪ (ℓ "丫俍") ⟫ʷ ≈ ⟪ (ℓ "俊丫") ⟫ʷ
lem-comm-push-SBOX⟨2·4·10·3⟩-sw0-R c4 = derive (ℓ "丫俍") (ℓ "俊丫")
  (re 1 1 (ℓ "佝亓俋亓俌") ∷
   rw 0 (q26 c4) ∷
   rw 1 (q2 c4) ∷
   rw 2 (q27 c4) ∷
   rw 3 (q2 c4) ∷
   rw 4 (q28 c4) ∷
   re 0 5 (ℓ "俊") ∷ []) Eq.refl

private
  q29 : WsL → Eqn
  q29 c4 = sE 2564 (lem-comm-push-BOX⟨4·0312⟩-sw2-R c4)
  q30 : WsL → Eqn
  q30 c4 = sE 2553 (lem-comm-push-SBOX⟨4·0·2·1⟩-sw2-R c4)
  q31 : WsL → Eqn
  q31 c4 = sE 2547 (lem-comm-push-SBOXd⟨4·0·2·1⟩-sw2-R c4)

-- comm push SBOX(4;0;31;2) sw2 R: 7 steps
lem-comm-push-SBOX⟨4·0·31·2⟩-sw2-R : WsL → ⟪ (ℓ "乥俨") ⟫ʷ ≈ ⟪ (ℓ "俦乥") ⟫ʷ
lem-comm-push-SBOX⟨4·0·31·2⟩-sw2-R c4 = derive (ℓ "乥俨") (ℓ "俦乥")
  (re 1 1 (ℓ "侐亦俣亦俧") ∷
   rw 0 (q29 c4) ∷
   rw 1 (q10 c4) ∷
   rw 2 (q30 c4) ∷
   rw 3 (q10 c4) ∷
   rw 4 (q31 c4) ∷
   re 0 5 (ℓ "俦") ∷ []) Eq.refl

private
  q32 : WsL → Eqn
  q32 c4 = sE 2563 (lem-comm-push-BOX⟨4·0123⟩-sw0-R c4)
  q33 : WsL → Eqn
  q33 c4 = sE 2554 (lem-comm-push-SBOX⟨4·0·3·2⟩-sw0-R c4)
  q34 : WsL → Eqn
  q34 c4 = sE 2548 (lem-comm-push-SBOXd⟨4·0·3·2⟩-sw0-R c4)

-- comm push SBOX(4;0;12;3) sw0 R: 7 steps
lem-comm-push-SBOX⟨4·0·12·3⟩-sw0-R : WsL → ⟪ (ℓ "丫俢") ⟫ʷ ≈ ⟪ (ℓ "俭丫") ⟫ʷ
lem-comm-push-SBOX⟨4·0·12·3⟩-sw0-R c4 = derive (ℓ "丫俢") (ℓ "俭丫")
  (re 1 1 (ℓ "侍产俠产信") ∷
   rw 0 (q32 c4) ∷
   rw 1 (q6 c4) ∷
   rw 2 (q33 c4) ∷
   rw 3 (q6 c4) ∷
   rw 4 (q34 c4) ∷
   re 0 5 (ℓ "俭") ∷ []) Eq.refl

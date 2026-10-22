{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD117 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D117 (Sᴰ : SD117) where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-comm-push-SBOX⟨2·1·43·0⟩-sw2-R ; lem-comm-push-SBOX⟨3·1·42·0⟩-sw3-R ; lem-comm-push-SBOX⟨4·1·32·0⟩-sw2-R)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-comm-push-SBOX⟨0·2·43·1⟩-sw0-R ; lem-comm-push-SBOX⟨1·2·43·0⟩-sw1-R ; lem-comm-push-SBOX⟨4·0·21·3⟩-sw1-R ; lem-comm-push-SBOX⟨4·1·23·0⟩-sw1-R ; lem-comm-push-SBOX⟨4·2·13·0⟩-sw0-R)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-comm-push-SBOX⟨4·0·12·3⟩-sw0-R ; lem-comm-push-SBOX⟨4·0·31·2⟩-sw2-R)

-- The lemmas of other derivation modules (DSig).
private
  lem-F4-I-K1-at0440 : Ws → St 1453
  lem-F4-I-K1-at0440 = pickᴰ 0 Sᴰ
  lem-F4-I-K2-at0440 : Ws → St 1454
  lem-F4-I-K2-at0440 = pickᴰ 1 Sᴰ
  lem-F4-K2-K1-at0440 : Ws → St 1602
  lem-F4-K2-K1-at0440 = pickᴰ 2 Sᴰ
  lem-F4-K2-K2-at0440 : Ws → St 1603
  lem-F4-K2-K2-at0440 = pickᴰ 3 Sᴰ
  lem-F4-CS1-CS1-at0440 : Ws → St 1604
  lem-F4-CS1-CS1-at0440 = pickᴰ 4 Sᴰ
  lem-F4-CS1-K1-at0440 : Ws → St 1605
  lem-F4-CS1-K1-at0440 = pickᴰ 5 Sᴰ
  lem-F4-I-CS1-at0440 : Ws → St 1460
  lem-F4-I-CS1-at0440 = pickᴰ 6 Sᴰ
  lem-F4-CS2-CS2-at0440 : Ws → St 1606
  lem-F4-CS2-CS2-at0440 = pickᴰ 7 Sᴰ
  lem-F4-CS2-I-at0440 : Ws → St 1607
  lem-F4-CS2-I-at0440 = pickᴰ 8 Sᴰ
  lem-F4-CS2-K2-at0440 : Ws → St 1608
  lem-F4-CS2-K2-at0440 = pickᴰ 9 Sᴰ
  lem-F4-I-CS2-at0440 : Ws → St 1462
  lem-F4-I-CS2-at0440 = pickᴰ 10 Sᴰ
  lem-F4-K2-CS2-at0440 : Ws → St 1609
  lem-F4-K2-CS2-at0440 = pickᴰ 11 Sᴰ
  lem-F5-23 : Ws → St 1377
  lem-F5-23 = pickᴰ 12 Sᴰ
  lem-F4-CS2-K1-at0440 : Ws → St 1610
  lem-F4-CS2-K1-at0440 = pickᴰ 13 Sᴰ
  lem-F4-CS1-K2-at0440 : Ws → St 1611
  lem-F4-CS1-K2-at0440 = pickᴰ 14 Sᴰ
  lem-F4-CS1-CS2-at0440 : Ws → St 1612
  lem-F4-CS1-CS2-at0440 = pickᴰ 15 Sᴰ
  lem-F4-CS2-CS1-at0440 : Ws → St 1613
  lem-F4-CS2-CS1-at0440 = pickᴰ 16 Sᴰ
  lem-F4-K2-CS1-at0440 : Ws → St 1614
  lem-F4-K2-CS1-at0440 = pickᴰ 17 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = wlE 1457 (lit c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (Sw23 ∷ Sb4-0-31-2 ∷ []) (Sb4-0-21-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨4·0·31·2⟩-sw2-R (lit c4))
  q3 : Ws → Eqn
  q3 c4 = wlE 3 (lit c4)
  q4 : Ws → Eqn
  q4 c4 = wlE 1458 (lit c4)
  q5 : Ws → Eqn
  q5 c4 = eqn (Sw12 ∷ Sb4-0-21-3 ∷ []) (Sb4-0-12-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨4·0·21·3⟩-sw1-R (lit c4))
  q6 : Ws → Eqn
  q6 c4 = wlE 6 (lit c4)
  q7 : Ws → Eqn
  q7 c4 = wlE 1459 (lit c4)
  q8 : Ws → Eqn
  q8 c4 = eqn (Sw01 ∷ Sb4-0-12-3 ∷ []) (Sb4-1-02-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨4·0·12·3⟩-sw0-R (lit c4))
  q9 : Ws → Eqn
  q9 c4 = wlE 18 (lit c4)
  q10 : Ws → Eqn
  q10 c4 = sE 1604 (lem-F4-CS1-CS1-at0440 c4)
  q11 : Ws → Eqn
  q11 c4 = sE 1611 (lem-F4-CS1-K2-at0440 c4)
  q12 : Ws → Eqn
  q12 c4 = sE 1612 (lem-F4-CS1-CS2-at0440 c4)
  q13 : Ws → Eqn
  q13 c4 = sE 1605 (lem-F4-CS1-K1-at0440 c4)
  q14 : Ws → Eqn
  q14 c4 = wlE 1715 (lit c4)
  q15 : Ws → Eqn
  q15 c4 = sE 1614 (lem-F4-K2-CS1-at0440 c4)
  q16 : Ws → Eqn
  q16 c4 = sE 1603 (lem-F4-K2-K2-at0440 c4)
  q17 : Ws → Eqn
  q17 c4 = sE 1609 (lem-F4-K2-CS2-at0440 c4)
  q18 : Ws → Eqn
  q18 c4 = sE 1602 (lem-F4-K2-K1-at0440 c4)
  q19 : Ws → Eqn
  q19 c4 = wlE 1461 (lit c4)
  q20 : Ws → Eqn
  q20 c4 = sE 1454 (lem-F4-I-K2-at0440 c4)
  q21 : Ws → Eqn
  q21 c4 = sE 1460 (lem-F4-I-CS1-at0440 c4)
  q22 : Ws → Eqn
  q22 c4 = sE 1462 (lem-F4-I-CS2-at0440 c4)
  q23 : Ws → Eqn
  q23 c4 = sE 1453 (lem-F4-I-K1-at0440 c4)
  q24 : Ws → Eqn
  q24 c4 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (c₂ (Swap) (CS))
  q25 : Ws → Eqn
  q25 c4 = wlE 47 (lit c4)
  q26 : Ws → Eqn
  q26 c4 = wlE 4 (lit c4)
  q27 : Ws → Eqn
  q27 c4 = eqn (CS12 ∷ Sw34 ∷ []) (Sw34 ∷ CS12 ∷ []) (c₃ (CS ↑) (Swap))
  q28 : Ws → Eqn
  q28 c4 = wlE 46 (lit c4)
  q29 : Ws → Eqn
  q29 c4 = sE 1377 (lem-F5-23 c4)
  q30 : Ws → Eqn
  q30 c4 = eqn (Sw01 ∷ X4 ∷ []) (X4 ∷ Sw01 ∷ []) (c₂ (Swap) (X ↑ ↑))
  q31 : Ws → Eqn
  q31 c4 = eqn (Sw01 ∷ Sb0-2-43-1 ∷ []) (Sb1-2-43-0 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw0-R (lit c4))
  q32 : Ws → Eqn
  q32 c4 = eqn (Sw12 ∷ X4 ∷ []) (X4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (X ↑))
  q33 : Ws → Eqn
  q33 c4 = eqn (Sw12 ∷ Sb1-2-43-0 ∷ []) (Sb2-1-43-0 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·2·43·0⟩-sw1-R (lit c4))
  q34 : Ws → Eqn
  q34 c4 = eqn (Sw23 ∷ X4 ∷ []) (X4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (X))
  q35 : Ws → Eqn
  q35 c4 = eqn (Sw23 ∷ Sb2-1-43-0 ∷ []) (Sb3-1-42-0 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨2·1·43·0⟩-sw2-R (lit c4))
  q36 : Ws → Eqn
  q36 c4 = wlE 1456 (lit c4)
  q37 : Ws → Eqn
  q37 c4 = eqn (Sw34 ∷ Sb3-1-42-0 ∷ []) (Sb4-1-32-0 ∷ Sw34 ∷ []) (lem-comm-push-SBOX⟨3·1·42·0⟩-sw3-R (lit c4))
  q38 : Ws → Eqn
  q38 c4 = eqn (Sw23 ∷ Sb4-1-32-0 ∷ []) (Sb4-1-23-0 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨4·1·32·0⟩-sw2-R (lit c4))
  q39 : Ws → Eqn
  q39 c4 = eqn (Sw12 ∷ Sb4-1-23-0 ∷ []) (Sb4-2-13-0 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨4·1·23·0⟩-sw1-R (lit c4))
  q40 : Ws → Eqn
  q40 c4 = eqn (Sw01 ∷ Sb4-2-13-0 ∷ []) (Sb4-2-03-1 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨4·2·13·0⟩-sw0-R (lit c4))
  q41 : Ws → Eqn
  q41 c4 = sE 1607 (lem-F4-CS2-I-at0440 c4)
  q42 : Ws → Eqn
  q42 c4 = sE 1608 (lem-F4-CS2-K2-at0440 c4)
  q43 : Ws → Eqn
  q43 c4 = sE 1613 (lem-F4-CS2-CS1-at0440 c4)
  q44 : Ws → Eqn
  q44 c4 = sE 1606 (lem-F4-CS2-CS2-at0440 c4)
  q45 : Ws → Eqn
  q45 c4 = sE 1610 (lem-F4-CS2-K1-at0440 c4)

-- ckt-TST @0440 part15: 111 steps
lem-ckt-TST-at0440-part15 : Ws → ⟪ (X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK01 ∷ S0 ∷ Sb2-4-01-3 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ X3 ∷ Sb4-0-31-2 ∷ X3 ∷ Sb4-0-31-2 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ K2 ∷ ι ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK01 ∷ S0 ∷ Sb2-4-01-3 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ X4 ∷ Sb1-2-43-0 ∷ X4 ∷ Sw01 ∷ Sb0-2-43-1 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ []) ⟫ʷ
lem-ckt-TST-at0440-part15 c4 = derive (X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK01 ∷ S0 ∷ Sb2-4-01-3 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ X3 ∷ Sb4-0-31-2 ∷ X3 ∷ Sb4-0-31-2 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ K2 ∷ ι ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ []) (X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK01 ∷ S0 ∷ Sb2-4-01-3 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ X4 ∷ Sb1-2-43-0 ∷ X4 ∷ Sw01 ∷ Sb0-2-43-1 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ [])
  (rw 211 (q1 c4) ∷
   rw 212 (q2 c4) ∷
   rw 213 (q1 c4) ∷
   rw 214 (q2 c4) ∷
   rw 215 (q3 c4) ∷
   rw 210 (q4 c4) ∷
   rw 211 (q5 c4) ∷
   rw 212 (q4 c4) ∷
   rw 213 (q5 c4) ∷
   rw 214 (q6 c4) ∷
   rw 209 (q7 c4) ∷
   rw 210 (q8 c4) ∷
   rw 211 (q7 c4) ∷
   rw 212 (q8 c4) ∷
   rw 213 (q9 c4) ∷
   rw⁻ 208 (q10 c4) ∷
   rw⁻ 207 (q11 c4) ∷
   rw⁻ 206 (q12 c4) ∷
   rw⁻ 205 (q13 c4) ∷
   rw 213 (q14 c4) ∷
   rw⁻ 212 (q15 c4) ∷
   rw⁻ 211 (q15 c4) ∷
   rw⁻ 210 (q16 c4) ∷
   rw⁻ 209 (q17 c4) ∷
   rw⁻ 208 (q18 c4) ∷
   rw⁻ 217 (q19 c4) ∷
   rw⁻ 216 (q20 c4) ∷
   rw⁻ 215 (q21 c4) ∷
   rw⁻ 214 (q21 c4) ∷
   rw⁻ 213 (q20 c4) ∷
   rw⁻ 212 (q22 c4) ∷
   rw⁻ 211 (q23 c4) ∷
   rw⁻ 222 (q9 c4) ∷
   rw⁻ 221 (q24 c4) ∷
   rw⁻ 223 (q6 c4) ∷
   rw 222 (q25 c4) ∷
   rw⁻ 224 (q3 c4) ∷
   re 223 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 225 (q3 c4) ∷
   rw⁻ 225 (q26 c4) ∷
   rw 224 (q27 c4) ∷
   rw⁻ 226 (q3 c4) ∷
   rw⁻ 225 (q3 c4) ∷
   re 226 3 (CS13 ∷ []) ∷
   rw⁻ 227 (q6 c4) ∷
   rw 226 (q28 c4) ∷
   rw⁻ 228 (q9 c4) ∷
   rw⁻ 227 (q24 c4) ∷
   rw⁻ 228 (q29 c4) ∷
   rw 227 (q30 c4) ∷
   rw 228 (q31 c4) ∷
   rw 229 (q30 c4) ∷
   rw 230 (q31 c4) ∷
   rw 231 (q9 c4) ∷
   rw 226 (q32 c4) ∷
   rw 227 (q33 c4) ∷
   rw 228 (q32 c4) ∷
   rw 229 (q33 c4) ∷
   rw 230 (q6 c4) ∷
   rw 225 (q34 c4) ∷
   rw 226 (q35 c4) ∷
   rw 227 (q34 c4) ∷
   rw 228 (q35 c4) ∷
   rw 229 (q3 c4) ∷
   rw 224 (q36 c4) ∷
   rw 225 (q37 c4) ∷
   rw 226 (q36 c4) ∷
   rw 227 (q37 c4) ∷
   rw 228 (q26 c4) ∷
   rw 223 (q1 c4) ∷
   rw 224 (q38 c4) ∷
   rw 225 (q1 c4) ∷
   rw 226 (q38 c4) ∷
   rw 227 (q3 c4) ∷
   rw 222 (q4 c4) ∷
   rw 223 (q39 c4) ∷
   rw 224 (q4 c4) ∷
   rw 225 (q39 c4) ∷
   rw 226 (q6 c4) ∷
   rw 221 (q7 c4) ∷
   rw 222 (q40 c4) ∷
   rw 223 (q7 c4) ∷
   rw 224 (q40 c4) ∷
   rw 225 (q9 c4) ∷
   rw⁻ 220 (q41 c4) ∷
   rw⁻ 219 (q42 c4) ∷
   rw⁻ 218 (q43 c4) ∷
   rw⁻ 217 (q43 c4) ∷
   rw⁻ 216 (q42 c4) ∷
   rw⁻ 215 (q44 c4) ∷
   rw⁻ 214 (q45 c4) ∷
   rw⁻ 226 (q9 c4) ∷
   rw⁻ 225 (q24 c4) ∷
   rw⁻ 227 (q6 c4) ∷
   rw 226 (q25 c4) ∷
   rw⁻ 228 (q3 c4) ∷
   re 227 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 229 (q3 c4) ∷
   rw⁻ 229 (q26 c4) ∷
   rw 228 (q27 c4) ∷
   rw⁻ 230 (q3 c4) ∷
   rw⁻ 229 (q3 c4) ∷
   re 230 3 (CS13 ∷ []) ∷
   rw⁻ 231 (q6 c4) ∷
   rw 230 (q28 c4) ∷
   rw⁻ 232 (q9 c4) ∷
   rw⁻ 231 (q24 c4) ∷
   rw⁻ 232 (q29 c4) ∷
   rw 231 (q30 c4) ∷
   rw 232 (q31 c4) ∷
   rw 233 (q30 c4) ∷ []) Eq.refl

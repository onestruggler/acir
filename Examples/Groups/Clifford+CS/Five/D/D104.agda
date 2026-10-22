{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD104 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D104 (Sᴰ : SD104) where

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
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-comm-push-SBOX⟨0·1·42·3⟩-sw0-R ; lem-comm-push-SBOX⟨0·2·43·1⟩-sw0-R ; lem-comm-push-SBOX⟨1·0·42·3⟩-sw1-R ; lem-comm-push-SBOX⟨1·2·43·0⟩-sw1-R ; lem-comm-push-SBOX⟨2·0·41·3⟩-sw2-R ; lem-comm-push-SBOX⟨3·0·41·2⟩-sw3-R ; lem-comm-push-SBOX⟨4·0·21·3⟩-sw1-R ; lem-comm-push-SBOX⟨4·1·23·0⟩-sw1-R ; lem-comm-push-SBOX⟨4·2·13·0⟩-sw0-R)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-comm-push-SBOX⟨4·0·12·3⟩-sw0-R ; lem-comm-push-SBOX⟨4·0·31·2⟩-sw2-R)

-- The lemmas of other derivation modules (DSig).
private
  lem-F4-K2-I-at0440 : Ws → St 1615
  lem-F4-K2-I-at0440 = pickᴰ 0 Sᴰ
  lem-F4-K2-K1-at0440 : Ws → St 1602
  lem-F4-K2-K1-at0440 = pickᴰ 1 Sᴰ
  lem-F4-K2-K2-at0440 : Ws → St 1603
  lem-F4-K2-K2-at0440 = pickᴰ 2 Sᴰ
  lem-F4-CS1-CS1-at0440 : Ws → St 1604
  lem-F4-CS1-CS1-at0440 = pickᴰ 3 Sᴰ
  lem-F4-CS1-I-at0440 : Ws → St 1616
  lem-F4-CS1-I-at0440 = pickᴰ 4 Sᴰ
  lem-F4-CS1-K1-at0440 : Ws → St 1605
  lem-F4-CS1-K1-at0440 = pickᴰ 5 Sᴰ
  lem-F4-CS2-CS2-at0440 : Ws → St 1606
  lem-F4-CS2-CS2-at0440 = pickᴰ 6 Sᴰ
  lem-F4-CS2-I-at0440 : Ws → St 1607
  lem-F4-CS2-I-at0440 = pickᴰ 7 Sᴰ
  lem-F4-CS2-K2-at0440 : Ws → St 1608
  lem-F4-CS2-K2-at0440 = pickᴰ 8 Sᴰ
  lem-F4-K2-CS2-at0440 : Ws → St 1609
  lem-F4-K2-CS2-at0440 = pickᴰ 9 Sᴰ
  lem-F5-12 : Ws → St 1580
  lem-F5-12 = pickᴰ 10 Sᴰ
  lem-F5-23 : Ws → St 1377
  lem-F5-23 = pickᴰ 11 Sᴰ
  lem-F4-CS2-K1-at0440 : Ws → St 1610
  lem-F4-CS2-K1-at0440 = pickᴰ 12 Sᴰ
  lem-F4-CS1-K2-at0440 : Ws → St 1611
  lem-F4-CS1-K2-at0440 = pickᴰ 13 Sᴰ
  lem-F4-CS1-CS2-at0440 : Ws → St 1612
  lem-F4-CS1-CS2-at0440 = pickᴰ 14 Sᴰ
  lem-F4-CS2-CS1-at0440 : Ws → St 1613
  lem-F4-CS2-CS1-at0440 = pickᴰ 15 Sᴰ
  lem-F4-K2-CS1-at0440 : Ws → St 1614
  lem-F4-K2-CS1-at0440 = pickᴰ 16 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = wlE 46 (lit c4)
  q2 : Ws → Eqn
  q2 c4 = wlE 18 (lit c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (c₂ (Swap) (CS))
  q4 : Ws → Eqn
  q4 c4 = sE 1377 (lem-F5-23 c4)
  q5 : Ws → Eqn
  q5 c4 = eqn (Sw01 ∷ X4 ∷ []) (X4 ∷ Sw01 ∷ []) (c₂ (Swap) (X ↑ ↑))
  q6 : Ws → Eqn
  q6 c4 = eqn (Sw01 ∷ Sb0-2-43-1 ∷ []) (Sb1-2-43-0 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw0-R (lit c4))
  q7 : Ws → Eqn
  q7 c4 = eqn (Sw12 ∷ X4 ∷ []) (X4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (X ↑))
  q8 : Ws → Eqn
  q8 c4 = eqn (Sw12 ∷ Sb1-2-43-0 ∷ []) (Sb2-1-43-0 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·2·43·0⟩-sw1-R (lit c4))
  q9 : Ws → Eqn
  q9 c4 = wlE 6 (lit c4)
  q10 : Ws → Eqn
  q10 c4 = eqn (Sw23 ∷ X4 ∷ []) (X4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (X))
  q11 : Ws → Eqn
  q11 c4 = eqn (Sw23 ∷ Sb2-1-43-0 ∷ []) (Sb3-1-42-0 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨2·1·43·0⟩-sw2-R (lit c4))
  q12 : Ws → Eqn
  q12 c4 = wlE 3 (lit c4)
  q13 : Ws → Eqn
  q13 c4 = wlE 1456 (lit c4)
  q14 : Ws → Eqn
  q14 c4 = eqn (Sw34 ∷ Sb3-1-42-0 ∷ []) (Sb4-1-32-0 ∷ Sw34 ∷ []) (lem-comm-push-SBOX⟨3·1·42·0⟩-sw3-R (lit c4))
  q15 : Ws → Eqn
  q15 c4 = wlE 4 (lit c4)
  q16 : Ws → Eqn
  q16 c4 = wlE 1457 (lit c4)
  q17 : Ws → Eqn
  q17 c4 = eqn (Sw23 ∷ Sb4-1-32-0 ∷ []) (Sb4-1-23-0 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨4·1·32·0⟩-sw2-R (lit c4))
  q18 : Ws → Eqn
  q18 c4 = wlE 1458 (lit c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (Sw12 ∷ Sb4-1-23-0 ∷ []) (Sb4-2-13-0 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨4·1·23·0⟩-sw1-R (lit c4))
  q20 : Ws → Eqn
  q20 c4 = wlE 1459 (lit c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (Sw01 ∷ Sb4-2-13-0 ∷ []) (Sb4-2-03-1 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨4·2·13·0⟩-sw0-R (lit c4))
  q22 : Ws → Eqn
  q22 c4 = sE 1606 (lem-F4-CS2-CS2-at0440 c4)
  q23 : Ws → Eqn
  q23 c4 = sE 1607 (lem-F4-CS2-I-at0440 c4)
  q24 : Ws → Eqn
  q24 c4 = sE 1608 (lem-F4-CS2-K2-at0440 c4)
  q25 : Ws → Eqn
  q25 c4 = sE 1613 (lem-F4-CS2-CS1-at0440 c4)
  q26 : Ws → Eqn
  q26 c4 = sE 1610 (lem-F4-CS2-K1-at0440 c4)
  q27 : Ws → Eqn
  q27 c4 = wlE 47 (lit c4)
  q28 : Ws → Eqn
  q28 c4 = eqn (CS12 ∷ Sw34 ∷ []) (Sw34 ∷ CS12 ∷ []) (c₃ (CS ↑) (Swap))
  q29 : Ws → Eqn
  q29 c4 = wlE 1715 (lit c4)
  q30 : Ws → Eqn
  q30 c4 = sE 1609 (lem-F4-K2-CS2-at0440 c4)
  q31 : Ws → Eqn
  q31 c4 = sE 1615 (lem-F4-K2-I-at0440 c4)
  q32 : Ws → Eqn
  q32 c4 = sE 1603 (lem-F4-K2-K2-at0440 c4)
  q33 : Ws → Eqn
  q33 c4 = sE 1614 (lem-F4-K2-CS1-at0440 c4)
  q34 : Ws → Eqn
  q34 c4 = sE 1602 (lem-F4-K2-K1-at0440 c4)
  q35 : Ws → Eqn
  q35 c4 = wlE 146 (lit c4)
  q36 : Ws → Eqn
  q36 c4 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (c₂ (CS) (Swap))
  q37 : Ws → Eqn
  q37 c4 = eqn (CS01 ∷ Sw34 ∷ []) (Sw34 ∷ CS01 ∷ []) (c₂ (CS) (Swap ↑))
  q38 : Ws → Eqn
  q38 c4 = wlE 24 (lit c4)
  q39 : Ws → Eqn
  q39 c4 = sE 1580 (lem-F5-12 c4)
  q40 : Ws → Eqn
  q40 c4 = eqn (Sw01 ∷ Sb0-1-42-3 ∷ []) (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw0-R (lit c4))
  q41 : Ws → Eqn
  q41 c4 = eqn (Sw12 ∷ Sb1-0-42-3 ∷ []) (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·0·42·3⟩-sw1-R (lit c4))
  q42 : Ws → Eqn
  q42 c4 = eqn (Sw23 ∷ Sb2-0-41-3 ∷ []) (Sb3-0-41-2 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨2·0·41·3⟩-sw2-R (lit c4))
  q43 : Ws → Eqn
  q43 c4 = eqn (Sw34 ∷ Sb3-0-41-2 ∷ []) (Sb4-0-31-2 ∷ Sw34 ∷ []) (lem-comm-push-SBOX⟨3·0·41·2⟩-sw3-R (lit c4))
  q44 : Ws → Eqn
  q44 c4 = eqn (Sw23 ∷ Sb4-0-31-2 ∷ []) (Sb4-0-21-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨4·0·31·2⟩-sw2-R (lit c4))
  q45 : Ws → Eqn
  q45 c4 = eqn (Sw12 ∷ Sb4-0-21-3 ∷ []) (Sb4-0-12-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨4·0·21·3⟩-sw1-R (lit c4))
  q46 : Ws → Eqn
  q46 c4 = eqn (Sw01 ∷ Sb4-0-12-3 ∷ []) (Sb4-1-02-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨4·0·12·3⟩-sw0-R (lit c4))
  q47 : Ws → Eqn
  q47 c4 = sE 1611 (lem-F4-CS1-K2-at0440 c4)
  q48 : Ws → Eqn
  q48 c4 = sE 1612 (lem-F4-CS1-CS2-at0440 c4)
  q49 : Ws → Eqn
  q49 c4 = sE 1616 (lem-F4-CS1-I-at0440 c4)
  q50 : Ws → Eqn
  q50 c4 = sE 1604 (lem-F4-CS1-CS1-at0440 c4)
  q51 : Ws → Eqn
  q51 c4 = sE 1605 (lem-F4-CS1-K1-at0440 c4)

-- ckt-TST @0440 part1: 220 steps
lem-ckt-TST-at0440-part1 : Ws → ⟪ (X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw23 ∷ CS13 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ Sb2-4-01-3 ∷ K1 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sw01 ∷ Sw12 ∷ X2 ∷ Sw23 ∷ Sb4-0-31-2 ∷ X3 ∷ Sb4-0-31-2 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ Sb2-4-01-3 ∷ K1 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ []) ⟫ʷ
lem-ckt-TST-at0440-part1 c4 = derive (X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw23 ∷ CS13 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ Sb2-4-01-3 ∷ K1 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ []) (X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sw01 ∷ Sw12 ∷ X2 ∷ Sw23 ∷ Sb4-0-31-2 ∷ X3 ∷ Sb4-0-31-2 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ Sb2-4-01-3 ∷ K1 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ [])
  (rw 37 (q1 c4) ∷
   rw⁻ 39 (q2 c4) ∷
   rw⁻ 38 (q3 c4) ∷
   rw⁻ 39 (q4 c4) ∷
   rw 38 (q5 c4) ∷
   rw 39 (q6 c4) ∷
   rw 40 (q5 c4) ∷
   rw 41 (q6 c4) ∷
   rw 42 (q2 c4) ∷
   rw 37 (q7 c4) ∷
   rw 38 (q8 c4) ∷
   rw 39 (q7 c4) ∷
   rw 40 (q8 c4) ∷
   rw 41 (q9 c4) ∷
   rw 36 (q10 c4) ∷
   rw 37 (q11 c4) ∷
   rw 38 (q10 c4) ∷
   rw 39 (q11 c4) ∷
   rw 40 (q12 c4) ∷
   rw 35 (q13 c4) ∷
   rw 36 (q14 c4) ∷
   rw 37 (q13 c4) ∷
   rw 38 (q14 c4) ∷
   rw 39 (q15 c4) ∷
   rw 34 (q16 c4) ∷
   rw 35 (q17 c4) ∷
   rw 36 (q16 c4) ∷
   rw 37 (q17 c4) ∷
   rw 38 (q12 c4) ∷
   rw 33 (q18 c4) ∷
   rw 34 (q19 c4) ∷
   rw 35 (q18 c4) ∷
   rw 36 (q19 c4) ∷
   rw 37 (q9 c4) ∷
   rw 32 (q20 c4) ∷
   rw 33 (q21 c4) ∷
   rw 34 (q20 c4) ∷
   rw 35 (q21 c4) ∷
   rw 36 (q2 c4) ∷
   rw⁻ 31 (q22 c4) ∷
   rw⁻ 30 (q23 c4) ∷
   rw⁻ 29 (q24 c4) ∷
   rw⁻ 28 (q25 c4) ∷
   rw⁻ 27 (q25 c4) ∷
   rw⁻ 26 (q24 c4) ∷
   rw⁻ 25 (q22 c4) ∷
   rw⁻ 24 (q26 c4) ∷
   rw⁻ 37 (q2 c4) ∷
   rw⁻ 36 (q3 c4) ∷
   rw⁻ 38 (q9 c4) ∷
   rw 37 (q27 c4) ∷
   rw⁻ 39 (q12 c4) ∷
   re 38 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 40 (q12 c4) ∷
   rw⁻ 40 (q15 c4) ∷
   rw 39 (q28 c4) ∷
   rw⁻ 41 (q12 c4) ∷
   rw⁻ 40 (q12 c4) ∷
   re 41 3 (CS13 ∷ []) ∷
   rw⁻ 42 (q9 c4) ∷
   rw 41 (q1 c4) ∷
   rw⁻ 43 (q2 c4) ∷
   rw⁻ 42 (q3 c4) ∷
   rw⁻ 43 (q4 c4) ∷
   rw 42 (q5 c4) ∷
   rw 43 (q6 c4) ∷
   rw 44 (q5 c4) ∷
   rw 45 (q6 c4) ∷
   rw 46 (q2 c4) ∷
   rw 41 (q7 c4) ∷
   rw 42 (q8 c4) ∷
   rw 43 (q7 c4) ∷
   rw 44 (q8 c4) ∷
   rw 45 (q9 c4) ∷
   rw 40 (q10 c4) ∷
   rw 41 (q11 c4) ∷
   rw 42 (q10 c4) ∷
   rw 43 (q11 c4) ∷
   rw 44 (q12 c4) ∷
   rw 39 (q13 c4) ∷
   rw 40 (q14 c4) ∷
   rw 41 (q13 c4) ∷
   rw 42 (q14 c4) ∷
   rw 43 (q15 c4) ∷
   rw 38 (q16 c4) ∷
   rw 39 (q17 c4) ∷
   rw 40 (q16 c4) ∷
   rw 41 (q17 c4) ∷
   rw 42 (q12 c4) ∷
   rw 37 (q18 c4) ∷
   rw 38 (q19 c4) ∷
   rw 39 (q18 c4) ∷
   rw 40 (q19 c4) ∷
   rw 41 (q9 c4) ∷
   rw 36 (q20 c4) ∷
   rw 37 (q21 c4) ∷
   rw 38 (q20 c4) ∷
   rw 39 (q21 c4) ∷
   rw 40 (q2 c4) ∷
   rw⁻ 35 (q22 c4) ∷
   rw⁻ 34 (q22 c4) ∷
   rw⁻ 33 (q23 c4) ∷
   rw⁻ 32 (q24 c4) ∷
   rw⁻ 31 (q25 c4) ∷
   rw⁻ 30 (q25 c4) ∷
   rw⁻ 29 (q24 c4) ∷
   rw⁻ 28 (q22 c4) ∷
   rw⁻ 27 (q26 c4) ∷
   rw 40 (q29 c4) ∷
   rw⁻ 39 (q30 c4) ∷
   rw⁻ 38 (q30 c4) ∷
   rw⁻ 37 (q30 c4) ∷
   rw⁻ 36 (q31 c4) ∷
   rw⁻ 35 (q32 c4) ∷
   rw⁻ 34 (q33 c4) ∷
   rw⁻ 33 (q33 c4) ∷
   rw⁻ 32 (q32 c4) ∷
   rw⁻ 31 (q30 c4) ∷
   rw⁻ 30 (q34 c4) ∷
   rw⁻ 45 (q2 c4) ∷
   rw 44 (q35 c4) ∷
   rw⁻ 46 (q9 c4) ∷
   re 45 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 47 (q9 c4) ∷
   rw⁻ 47 (q12 c4) ∷
   rw 46 (q36 c4) ∷
   rw⁻ 48 (q15 c4) ∷
   rw 47 (q37 c4) ∷
   rw⁻ 49 (q12 c4) ∷
   rw 48 (q36 c4) ∷
   rw⁻ 50 (q9 c4) ∷
   rw⁻ 49 (q9 c4) ∷
   re 50 3 (CS02 ∷ []) ∷
   rw⁻ 51 (q2 c4) ∷
   rw 50 (q38 c4) ∷
   rw⁻ 51 (q39 c4) ∷
   rw 50 (q5 c4) ∷
   rw 51 (q40 c4) ∷
   rw 52 (q5 c4) ∷
   rw 53 (q40 c4) ∷
   rw 54 (q2 c4) ∷
   rw 49 (q7 c4) ∷
   rw 50 (q41 c4) ∷
   rw 51 (q7 c4) ∷
   rw 52 (q41 c4) ∷
   rw 53 (q9 c4) ∷
   rw 48 (q10 c4) ∷
   rw 49 (q42 c4) ∷
   rw 50 (q10 c4) ∷
   rw 51 (q42 c4) ∷
   rw 52 (q12 c4) ∷
   rw 47 (q13 c4) ∷
   rw 48 (q43 c4) ∷
   rw 49 (q13 c4) ∷
   rw 50 (q43 c4) ∷
   rw 51 (q15 c4) ∷
   rw 46 (q16 c4) ∷
   rw 47 (q44 c4) ∷
   rw 48 (q16 c4) ∷
   rw 49 (q44 c4) ∷
   rw 50 (q12 c4) ∷
   rw 45 (q18 c4) ∷
   rw 46 (q45 c4) ∷
   rw 47 (q18 c4) ∷
   rw 48 (q45 c4) ∷
   rw 49 (q9 c4) ∷
   rw 44 (q20 c4) ∷
   rw 45 (q46 c4) ∷
   rw 46 (q20 c4) ∷
   rw 47 (q46 c4) ∷
   rw 48 (q2 c4) ∷
   rw⁻ 43 (q47 c4) ∷
   rw⁻ 42 (q48 c4) ∷
   rw⁻ 41 (q48 c4) ∷
   rw⁻ 40 (q48 c4) ∷
   rw⁻ 39 (q49 c4) ∷
   rw⁻ 38 (q47 c4) ∷
   rw⁻ 37 (q50 c4) ∷
   rw⁻ 36 (q50 c4) ∷
   rw⁻ 35 (q47 c4) ∷
   rw⁻ 34 (q48 c4) ∷
   rw⁻ 33 (q51 c4) ∷
   rw⁻ 49 (q2 c4) ∷
   rw 48 (q35 c4) ∷
   rw⁻ 50 (q9 c4) ∷
   re 49 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 51 (q9 c4) ∷
   rw⁻ 51 (q12 c4) ∷
   rw 50 (q36 c4) ∷
   rw⁻ 52 (q15 c4) ∷
   rw 51 (q37 c4) ∷
   rw⁻ 53 (q12 c4) ∷
   rw 52 (q36 c4) ∷
   rw⁻ 54 (q9 c4) ∷
   rw⁻ 53 (q9 c4) ∷
   re 54 3 (CS02 ∷ []) ∷
   rw⁻ 55 (q2 c4) ∷
   rw 54 (q38 c4) ∷
   rw⁻ 55 (q39 c4) ∷
   rw 54 (q5 c4) ∷
   rw 55 (q40 c4) ∷
   rw 56 (q5 c4) ∷
   rw 57 (q40 c4) ∷
   rw 58 (q2 c4) ∷
   rw 53 (q7 c4) ∷
   rw 54 (q41 c4) ∷
   rw 55 (q7 c4) ∷
   rw 56 (q41 c4) ∷
   rw 57 (q9 c4) ∷
   rw 52 (q10 c4) ∷
   rw 53 (q42 c4) ∷
   rw 54 (q10 c4) ∷
   rw 55 (q42 c4) ∷
   rw 56 (q12 c4) ∷
   rw 51 (q13 c4) ∷
   rw 52 (q43 c4) ∷
   rw 53 (q13 c4) ∷
   rw 54 (q43 c4) ∷
   rw 55 (q15 c4) ∷
   rw 50 (q16 c4) ∷ []) Eq.refl

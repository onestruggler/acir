{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD112 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D112 (Sᴰ : SD112) where

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
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-comm-push-SBOX⟨0·2·43·1⟩-sw0-R ; lem-comm-push-SBOX⟨1·2·43·0⟩-sw1-R ; lem-comm-push-SBOX⟨4·1·23·0⟩-sw1-R ; lem-comm-push-SBOX⟨4·2·13·0⟩-sw0-R)

-- The lemmas of other derivation modules (DSig).
private
  lem-F4-K2-I-at0440 : Ws → St 1615
  lem-F4-K2-I-at0440 = pickᴰ 0 Sᴰ
  lem-F4-K2-K2-at0440 : Ws → St 1603
  lem-F4-K2-K2-at0440 = pickᴰ 1 Sᴰ
  lem-F4-K2-K3-at0440 : Ws → St 1623
  lem-F4-K2-K3-at0440 = pickᴰ 2 Sᴰ
  lem-F4-CS2-CS2-at0440 : Ws → St 1606
  lem-F4-CS2-CS2-at0440 = pickᴰ 3 Sᴰ
  lem-F4-CS2-I-at0440 : Ws → St 1607
  lem-F4-CS2-I-at0440 = pickᴰ 4 Sᴰ
  lem-F4-CS2-K2-at0440 : Ws → St 1608
  lem-F4-CS2-K2-at0440 = pickᴰ 5 Sᴰ
  lem-F4-K2-CS2-at0440 : Ws → St 1609
  lem-F4-K2-CS2-at0440 = pickᴰ 6 Sᴰ
  lem-F5-23 : Ws → St 1377
  lem-F5-23 = pickᴰ 7 Sᴰ
  lem-F4-CS2-K1-at0440 : Ws → St 1610
  lem-F4-CS2-K1-at0440 = pickᴰ 8 Sᴰ
  lem-F4-CS2-CS1-at0440 : Ws → St 1613
  lem-F4-CS2-CS1-at0440 = pickᴰ 9 Sᴰ
  lem-F4-CS2-K3-at0440 : Ws → St 1621
  lem-F4-CS2-K3-at0440 = pickᴰ 10 Sᴰ
  lem-F4-K2-CS1-at0440 : Ws → St 1614
  lem-F4-K2-CS1-at0440 = pickᴰ 11 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 1621 (lem-F4-CS2-K3-at0440 c4)
  q2 : Ws → Eqn
  q2 c4 = sE 1606 (lem-F4-CS2-CS2-at0440 c4)
  q3 : Ws → Eqn
  q3 c4 = sE 1607 (lem-F4-CS2-I-at0440 c4)
  q4 : Ws → Eqn
  q4 c4 = sE 1608 (lem-F4-CS2-K2-at0440 c4)
  q5 : Ws → Eqn
  q5 c4 = sE 1613 (lem-F4-CS2-CS1-at0440 c4)
  q6 : Ws → Eqn
  q6 c4 = sE 1610 (lem-F4-CS2-K1-at0440 c4)
  q7 : Ws → Eqn
  q7 c4 = wlE 18 (lit c4)
  q8 : Ws → Eqn
  q8 c4 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (c₂ (Swap) (CS))
  q9 : Ws → Eqn
  q9 c4 = wlE 6 (lit c4)
  q10 : Ws → Eqn
  q10 c4 = wlE 47 (lit c4)
  q11 : Ws → Eqn
  q11 c4 = wlE 3 (lit c4)
  q12 : Ws → Eqn
  q12 c4 = wlE 4 (lit c4)
  q13 : Ws → Eqn
  q13 c4 = eqn (CS12 ∷ Sw34 ∷ []) (Sw34 ∷ CS12 ∷ []) (c₃ (CS ↑) (Swap))
  q14 : Ws → Eqn
  q14 c4 = wlE 46 (lit c4)
  q15 : Ws → Eqn
  q15 c4 = sE 1377 (lem-F5-23 c4)
  q16 : Ws → Eqn
  q16 c4 = eqn (Sw01 ∷ X4 ∷ []) (X4 ∷ Sw01 ∷ []) (c₂ (Swap) (X ↑ ↑))
  q17 : Ws → Eqn
  q17 c4 = eqn (Sw01 ∷ Sb0-2-43-1 ∷ []) (Sb1-2-43-0 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw0-R (lit c4))
  q18 : Ws → Eqn
  q18 c4 = eqn (Sw12 ∷ X4 ∷ []) (X4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (X ↑))
  q19 : Ws → Eqn
  q19 c4 = eqn (Sw12 ∷ Sb1-2-43-0 ∷ []) (Sb2-1-43-0 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·2·43·0⟩-sw1-R (lit c4))
  q20 : Ws → Eqn
  q20 c4 = eqn (Sw23 ∷ X4 ∷ []) (X4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (X))
  q21 : Ws → Eqn
  q21 c4 = eqn (Sw23 ∷ Sb2-1-43-0 ∷ []) (Sb3-1-42-0 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨2·1·43·0⟩-sw2-R (lit c4))
  q22 : Ws → Eqn
  q22 c4 = wlE 1456 (lit c4)
  q23 : Ws → Eqn
  q23 c4 = eqn (Sw34 ∷ Sb3-1-42-0 ∷ []) (Sb4-1-32-0 ∷ Sw34 ∷ []) (lem-comm-push-SBOX⟨3·1·42·0⟩-sw3-R (lit c4))
  q24 : Ws → Eqn
  q24 c4 = wlE 1457 (lit c4)
  q25 : Ws → Eqn
  q25 c4 = eqn (Sw23 ∷ Sb4-1-32-0 ∷ []) (Sb4-1-23-0 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨4·1·32·0⟩-sw2-R (lit c4))
  q26 : Ws → Eqn
  q26 c4 = wlE 1458 (lit c4)
  q27 : Ws → Eqn
  q27 c4 = eqn (Sw12 ∷ Sb4-1-23-0 ∷ []) (Sb4-2-13-0 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨4·1·23·0⟩-sw1-R (lit c4))
  q28 : Ws → Eqn
  q28 c4 = wlE 1459 (lit c4)
  q29 : Ws → Eqn
  q29 c4 = eqn (Sw01 ∷ Sb4-2-13-0 ∷ []) (Sb4-2-03-1 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨4·2·13·0⟩-sw0-R (lit c4))
  q30 : Ws → Eqn
  q30 c4 = wlE 1715 (lit c4)
  q31 : Ws → Eqn
  q31 c4 = sE 1609 (lem-F4-K2-CS2-at0440 c4)
  q32 : Ws → Eqn
  q32 c4 = sE 1603 (lem-F4-K2-K2-at0440 c4)
  q33 : Ws → Eqn
  q33 c4 = sE 1615 (lem-F4-K2-I-at0440 c4)
  q34 : Ws → Eqn
  q34 c4 = sE 1623 (lem-F4-K2-K3-at0440 c4)
  q35 : Ws → Eqn
  q35 c4 = sE 1614 (lem-F4-K2-CS1-at0440 c4)

-- ckt-TST @0440 part9: 138 steps
lem-ckt-TST-at0440-part9 : Ws → ⟪ (X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ Sb2-4-01-3 ∷ K1 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ X0 ∷ CK02 ∷ X0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ Sb2-4-01-3 ∷ K1 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ []) ⟫ʷ
lem-ckt-TST-at0440-part9 c4 = derive (X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ Sb2-4-01-3 ∷ K1 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ []) (X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ X0 ∷ CK02 ∷ X0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ Sb2-4-01-3 ∷ K1 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ [])
  (rw⁻ 139 (q1 c4) ∷
   rw⁻ 138 (q2 c4) ∷
   rw⁻ 137 (q2 c4) ∷
   rw⁻ 136 (q1 c4) ∷
   rw⁻ 135 (q3 c4) ∷
   rw⁻ 134 (q4 c4) ∷
   rw⁻ 133 (q2 c4) ∷
   rw⁻ 132 (q2 c4) ∷
   rw⁻ 131 (q4 c4) ∷
   rw⁻ 130 (q3 c4) ∷
   rw⁻ 129 (q1 c4) ∷
   rw⁻ 128 (q2 c4) ∷
   rw⁻ 127 (q2 c4) ∷
   rw⁻ 126 (q1 c4) ∷
   rw⁻ 125 (q3 c4) ∷
   rw⁻ 124 (q4 c4) ∷
   rw⁻ 123 (q5 c4) ∷
   rw⁻ 122 (q5 c4) ∷
   rw⁻ 121 (q4 c4) ∷
   rw⁻ 120 (q2 c4) ∷
   rw⁻ 119 (q2 c4) ∷
   rw⁻ 118 (q2 c4) ∷
   rw⁻ 117 (q3 c4) ∷
   rw⁻ 116 (q4 c4) ∷
   rw⁻ 115 (q5 c4) ∷
   rw⁻ 114 (q5 c4) ∷
   rw⁻ 113 (q4 c4) ∷
   rw⁻ 112 (q2 c4) ∷
   rw⁻ 111 (q6 c4) ∷
   rw⁻ 153 (q7 c4) ∷
   rw⁻ 152 (q8 c4) ∷
   rw⁻ 154 (q9 c4) ∷
   rw 153 (q10 c4) ∷
   rw⁻ 155 (q11 c4) ∷
   re 154 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 156 (q11 c4) ∷
   rw⁻ 156 (q12 c4) ∷
   rw 155 (q13 c4) ∷
   rw⁻ 157 (q11 c4) ∷
   rw⁻ 156 (q11 c4) ∷
   re 157 3 (CS13 ∷ []) ∷
   rw⁻ 158 (q9 c4) ∷
   rw 157 (q14 c4) ∷
   rw⁻ 159 (q7 c4) ∷
   rw⁻ 158 (q8 c4) ∷
   rw⁻ 159 (q15 c4) ∷
   rw 158 (q16 c4) ∷
   rw 159 (q17 c4) ∷
   rw 160 (q16 c4) ∷
   rw 161 (q17 c4) ∷
   rw 162 (q7 c4) ∷
   rw 157 (q18 c4) ∷
   rw 158 (q19 c4) ∷
   rw 159 (q18 c4) ∷
   rw 160 (q19 c4) ∷
   rw 161 (q9 c4) ∷
   rw 156 (q20 c4) ∷
   rw 157 (q21 c4) ∷
   rw 158 (q20 c4) ∷
   rw 159 (q21 c4) ∷
   rw 160 (q11 c4) ∷
   rw 155 (q22 c4) ∷
   rw 156 (q23 c4) ∷
   rw 157 (q22 c4) ∷
   rw 158 (q23 c4) ∷
   rw 159 (q12 c4) ∷
   rw 154 (q24 c4) ∷
   rw 155 (q25 c4) ∷
   rw 156 (q24 c4) ∷
   rw 157 (q25 c4) ∷
   rw 158 (q11 c4) ∷
   rw 153 (q26 c4) ∷
   rw 154 (q27 c4) ∷
   rw 155 (q26 c4) ∷
   rw 156 (q27 c4) ∷
   rw 157 (q9 c4) ∷
   rw 152 (q28 c4) ∷
   rw 153 (q29 c4) ∷
   rw 154 (q28 c4) ∷
   rw 155 (q29 c4) ∷
   rw 156 (q7 c4) ∷
   rw⁻ 151 (q2 c4) ∷
   rw⁻ 150 (q4 c4) ∷
   rw⁻ 149 (q3 c4) ∷
   rw⁻ 148 (q1 c4) ∷
   rw⁻ 147 (q2 c4) ∷
   rw⁻ 146 (q2 c4) ∷
   rw⁻ 145 (q1 c4) ∷
   rw⁻ 144 (q5 c4) ∷
   rw⁻ 143 (q3 c4) ∷
   rw⁻ 142 (q1 c4) ∷
   rw⁻ 141 (q2 c4) ∷
   rw⁻ 140 (q2 c4) ∷
   rw⁻ 139 (q1 c4) ∷
   rw⁻ 138 (q3 c4) ∷
   rw⁻ 137 (q4 c4) ∷
   rw⁻ 136 (q2 c4) ∷
   rw⁻ 135 (q2 c4) ∷
   rw⁻ 134 (q4 c4) ∷
   rw⁻ 133 (q3 c4) ∷
   rw⁻ 132 (q1 c4) ∷
   rw⁻ 131 (q2 c4) ∷
   rw⁻ 130 (q2 c4) ∷
   rw⁻ 129 (q1 c4) ∷
   rw⁻ 128 (q3 c4) ∷
   rw⁻ 127 (q4 c4) ∷
   rw⁻ 126 (q5 c4) ∷
   rw⁻ 125 (q5 c4) ∷
   rw⁻ 124 (q4 c4) ∷
   rw⁻ 123 (q2 c4) ∷
   rw⁻ 122 (q2 c4) ∷
   rw⁻ 121 (q2 c4) ∷
   rw⁻ 120 (q3 c4) ∷
   rw⁻ 119 (q4 c4) ∷
   rw⁻ 118 (q5 c4) ∷
   rw⁻ 117 (q5 c4) ∷
   rw⁻ 116 (q4 c4) ∷
   rw⁻ 115 (q2 c4) ∷
   rw⁻ 114 (q6 c4) ∷
   rw 156 (q30 c4) ∷
   rw⁻ 155 (q31 c4) ∷
   rw⁻ 154 (q31 c4) ∷
   rw⁻ 153 (q32 c4) ∷
   rw⁻ 152 (q33 c4) ∷
   rw⁻ 151 (q34 c4) ∷
   rw⁻ 150 (q31 c4) ∷
   rw⁻ 149 (q31 c4) ∷
   rw⁻ 148 (q34 c4) ∷
   rw⁻ 147 (q35 c4) ∷
   rw⁻ 146 (q33 c4) ∷
   rw⁻ 145 (q34 c4) ∷
   rw⁻ 144 (q31 c4) ∷
   rw⁻ 143 (q31 c4) ∷
   rw⁻ 142 (q34 c4) ∷
   rw⁻ 141 (q33 c4) ∷
   rw⁻ 140 (q32 c4) ∷
   rw⁻ 139 (q31 c4) ∷
   rw⁻ 138 (q31 c4) ∷ []) Eq.refl

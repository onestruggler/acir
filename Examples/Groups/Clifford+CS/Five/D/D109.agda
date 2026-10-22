{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD109 ; pickᴰ)

module Examples.Groups.Clifford+CS.Five.D.D109 (Sᴰ : SD109) where

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
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-comm-push-SBOX⟨0·1·42·3⟩-sw0-R ; lem-comm-push-SBOX⟨0·2·43·1⟩-sw0-R ; lem-comm-push-SBOX⟨1·0·42·3⟩-sw1-R ; lem-comm-push-SBOX⟨1·2·43·0⟩-sw1-R ; lem-comm-push-SBOX⟨2·0·41·3⟩-sw2-R ; lem-comm-push-SBOX⟨3·0·41·2⟩-sw3-R ; lem-comm-push-SBOX⟨4·0·21·3⟩-sw1-R ; lem-comm-push-SBOX⟨4·1·23·0⟩-sw1-R)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-comm-push-SBOX⟨4·0·12·3⟩-sw0-R ; lem-comm-push-SBOX⟨4·0·31·2⟩-sw2-R)

-- The lemmas of other derivation modules (DSig).
private
  lem-F4-K3-I-at0440 : Ws → St 1617
  lem-F4-K3-I-at0440 = pickᴰ 0 Sᴰ
  lem-F4-K3-K1-at0440 : Ws → St 1618
  lem-F4-K3-K1-at0440 = pickᴰ 1 Sᴰ
  lem-F4-K3-K2-at0440 : Ws → St 1619
  lem-F4-K3-K2-at0440 = pickᴰ 2 Sᴰ
  lem-F4-K3-K3-at0440 : Ws → St 1624
  lem-F4-K3-K3-at0440 = pickᴰ 3 Sᴰ
  lem-F4-CS1-CS1-at0440 : Ws → St 1604
  lem-F4-CS1-CS1-at0440 = pickᴰ 4 Sᴰ
  lem-F4-CS1-I-at0440 : Ws → St 1616
  lem-F4-CS1-I-at0440 = pickᴰ 5 Sᴰ
  lem-F4-CS1-K1-at0440 : Ws → St 1605
  lem-F4-CS1-K1-at0440 = pickᴰ 6 Sᴰ
  lem-F4-CS1-K3-at0440 : Ws → St 1625
  lem-F4-CS1-K3-at0440 = pickᴰ 7 Sᴰ
  lem-F4-K3-CS1-at0440 : Ws → St 1620
  lem-F4-K3-CS1-at0440 = pickᴰ 8 Sᴰ
  lem-F5-12 : Ws → St 1580
  lem-F5-12 = pickᴰ 9 Sᴰ
  lem-F5-23 : Ws → St 1377
  lem-F5-23 = pickᴰ 10 Sᴰ
  lem-F4-CS1-K2-at0440 : Ws → St 1611
  lem-F4-CS1-K2-at0440 = pickᴰ 11 Sᴰ
  lem-F4-CS1-CS2-at0440 : Ws → St 1612
  lem-F4-CS1-CS2-at0440 = pickᴰ 12 Sᴰ
  lem-F4-K3-CS2-at0440 : Ws → St 1622
  lem-F4-K3-CS2-at0440 = pickᴰ 13 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = eqn (CS01 ∷ Sw34 ∷ []) (Sw34 ∷ CS01 ∷ []) (c₂ (CS) (Swap ↑))
  q2 : Ws → Eqn
  q2 c4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wl 3 (lit c4))
  q3 : Ws → Eqn
  q3 c4 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (c₂ (CS) (Swap))
  q4 : Ws → Eqn
  q4 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl 6 (lit c4))
  q5 : Ws → Eqn
  q5 c4 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wl 18 (lit c4))
  q6 : Ws → Eqn
  q6 c4 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wl 24 (lit c4))
  q7 : Ws → Eqn
  q7 c4 = eqn (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (CS12 ∷ []) (lem-F5-12 c4)
  q8 : Ws → Eqn
  q8 c4 = eqn (Sw01 ∷ X4 ∷ []) (X4 ∷ Sw01 ∷ []) (c₂ (Swap) (X ↑ ↑))
  q9 : Ws → Eqn
  q9 c4 = eqn (Sw01 ∷ Sb0-1-42-3 ∷ []) (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw0-R (lit c4))
  q10 : Ws → Eqn
  q10 c4 = eqn (Sw12 ∷ X4 ∷ []) (X4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (X ↑))
  q11 : Ws → Eqn
  q11 c4 = eqn (Sw12 ∷ Sb1-0-42-3 ∷ []) (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·0·42·3⟩-sw1-R (lit c4))
  q12 : Ws → Eqn
  q12 c4 = eqn (Sw23 ∷ X4 ∷ []) (X4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (X))
  q13 : Ws → Eqn
  q13 c4 = eqn (Sw23 ∷ Sb2-0-41-3 ∷ []) (Sb3-0-41-2 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨2·0·41·3⟩-sw2-R (lit c4))
  q14 : Ws → Eqn
  q14 c4 = eqn (Sw34 ∷ X4 ∷ []) (X3 ∷ Sw34 ∷ []) (wl 1456 (lit c4))
  q15 : Ws → Eqn
  q15 c4 = eqn (Sw34 ∷ Sb3-0-41-2 ∷ []) (Sb4-0-31-2 ∷ Sw34 ∷ []) (lem-comm-push-SBOX⟨3·0·41·2⟩-sw3-R (lit c4))
  q16 : Ws → Eqn
  q16 c4 = eqn (Sw34 ∷ Sw34 ∷ []) [] (wl 4 (lit c4))
  q17 : Ws → Eqn
  q17 c4 = eqn (Sw23 ∷ X3 ∷ []) (X2 ∷ Sw23 ∷ []) (wl 1457 (lit c4))
  q18 : Ws → Eqn
  q18 c4 = eqn (Sw23 ∷ Sb4-0-31-2 ∷ []) (Sb4-0-21-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨4·0·31·2⟩-sw2-R (lit c4))
  q19 : Ws → Eqn
  q19 c4 = eqn (Sw12 ∷ X2 ∷ []) (X1 ∷ Sw12 ∷ []) (wl 1458 (lit c4))
  q20 : Ws → Eqn
  q20 c4 = eqn (Sw12 ∷ Sb4-0-21-3 ∷ []) (Sb4-0-12-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨4·0·21·3⟩-sw1-R (lit c4))
  q21 : Ws → Eqn
  q21 c4 = eqn (Sw01 ∷ X1 ∷ []) (X0 ∷ Sw01 ∷ []) (wl 1459 (lit c4))
  q22 : Ws → Eqn
  q22 c4 = eqn (Sw01 ∷ Sb4-0-12-3 ∷ []) (Sb4-1-02-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨4·0·12·3⟩-sw0-R (lit c4))
  q23 : Ws → Eqn
  q23 c4 = eqn (X0 ∷ Sb4-1-02-3 ∷ X0 ∷ S0 ∷ []) (S0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ []) (lem-F4-CS1-I-at0440 c4)
  q24 : Ws → Eqn
  q24 c4 = eqn (X0 ∷ Sb4-1-02-3 ∷ X0 ∷ CK03 ∷ []) (CK03 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ []) (lem-F4-CS1-K3-at0440 c4)
  q25 : Ws → Eqn
  q25 c4 = eqn (X0 ∷ Sb4-1-02-3 ∷ X0 ∷ Sb4-2-03-1 ∷ []) (Sb4-2-03-1 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ []) (lem-F4-CS1-CS2-at0440 c4)
  q26 : Ws → Eqn
  q26 c4 = eqn (X0 ∷ Sb4-1-02-3 ∷ X0 ∷ CK02 ∷ []) (CK02 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ []) (lem-F4-CS1-K2-at0440 c4)
  q27 : Ws → Eqn
  q27 c4 = eqn (X0 ∷ Sb4-1-02-3 ∷ X0 ∷ Sb4-1-02-3 ∷ []) (Sb4-1-02-3 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ []) (lem-F4-CS1-CS1-at0440 c4)
  q28 : Ws → Eqn
  q28 c4 = eqn (X0 ∷ Sb4-1-02-3 ∷ X0 ∷ CK01 ∷ []) (CK01 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ []) (lem-F4-CS1-K1-at0440 c4)
  q29 : Ws → Eqn
  q29 c4 = eqn (K3 ∷ []) (X0 ∷ CK03 ∷ X0 ∷ CK03 ∷ []) (wl 1716 (lit c4))
  q30 : Ws → Eqn
  q30 c4 = eqn (X0 ∷ CK03 ∷ X0 ∷ Sb4-1-02-3 ∷ []) (Sb4-1-02-3 ∷ X0 ∷ CK03 ∷ X0 ∷ []) (lem-F4-K3-CS1-at0440 c4)
  q31 : Ws → Eqn
  q31 c4 = eqn (X0 ∷ CK03 ∷ X0 ∷ S0 ∷ []) (S0 ∷ X0 ∷ CK03 ∷ X0 ∷ []) (lem-F4-K3-I-at0440 c4)
  q32 : Ws → Eqn
  q32 c4 = eqn (X0 ∷ CK03 ∷ X0 ∷ CK03 ∷ []) (CK03 ∷ X0 ∷ CK03 ∷ X0 ∷ []) (lem-F4-K3-K3-at0440 c4)
  q33 : Ws → Eqn
  q33 c4 = eqn (X0 ∷ CK03 ∷ X0 ∷ Sb4-2-03-1 ∷ []) (Sb4-2-03-1 ∷ X0 ∷ CK03 ∷ X0 ∷ []) (lem-F4-K3-CS2-at0440 c4)
  q34 : Ws → Eqn
  q34 c4 = eqn (X0 ∷ CK03 ∷ X0 ∷ CK02 ∷ []) (CK02 ∷ X0 ∷ CK03 ∷ X0 ∷ []) (lem-F4-K3-K2-at0440 c4)
  q35 : Ws → Eqn
  q35 c4 = eqn (X0 ∷ CK03 ∷ X0 ∷ CK01 ∷ []) (CK01 ∷ X0 ∷ CK03 ∷ X0 ∷ []) (lem-F4-K3-K1-at0440 c4)
  q36 : Ws → Eqn
  q36 c4 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (c₂ (Swap) (CS))
  q37 : Ws → Eqn
  q37 c4 = eqn (CS23 ∷ Sw12 ∷ []) (Sw12 ∷ CS13 ∷ []) (wl 47 (lit c4))
  q38 : Ws → Eqn
  q38 c4 = eqn (CS12 ∷ Sw34 ∷ []) (Sw34 ∷ CS12 ∷ []) (c₃ (CS ↑) (Swap))
  q39 : Ws → Eqn
  q39 c4 = eqn (CS13 ∷ Sw12 ∷ []) (Sw12 ∷ CS23 ∷ []) (wl 46 (lit c4))
  q40 : Ws → Eqn
  q40 c4 = eqn (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (CS23 ∷ []) (lem-F5-23 c4)
  q41 : Ws → Eqn
  q41 c4 = eqn (Sw01 ∷ Sb0-2-43-1 ∷ []) (Sb1-2-43-0 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw0-R (lit c4))
  q42 : Ws → Eqn
  q42 c4 = eqn (Sw12 ∷ Sb1-2-43-0 ∷ []) (Sb2-1-43-0 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·2·43·0⟩-sw1-R (lit c4))
  q43 : Ws → Eqn
  q43 c4 = eqn (Sw23 ∷ Sb2-1-43-0 ∷ []) (Sb3-1-42-0 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨2·1·43·0⟩-sw2-R (lit c4))
  q44 : Ws → Eqn
  q44 c4 = eqn (Sw34 ∷ Sb3-1-42-0 ∷ []) (Sb4-1-32-0 ∷ Sw34 ∷ []) (lem-comm-push-SBOX⟨3·1·42·0⟩-sw3-R (lit c4))
  q45 : Ws → Eqn
  q45 c4 = eqn (Sw23 ∷ Sb4-1-32-0 ∷ []) (Sb4-1-23-0 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨4·1·32·0⟩-sw2-R (lit c4))
  q46 : Ws → Eqn
  q46 c4 = eqn (Sw12 ∷ Sb4-1-23-0 ∷ []) (Sb4-2-13-0 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨4·1·23·0⟩-sw1-R (lit c4))

-- ckt-TST @0440 part6: 152 steps
lem-ckt-TST-at0440-part6 : Ws → ⟪ (X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ CS01 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ Sb2-4-01-3 ∷ K1 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sw01 ∷ X1 ∷ Sb4-2-13-0 ∷ X1 ∷ Sb4-2-13-0 ∷ Sw12 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ Sb2-4-01-3 ∷ K1 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ []) ⟫ʷ
lem-ckt-TST-at0440-part6 c4 = derive (X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ CS01 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ Sb2-4-01-3 ∷ K1 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ []) (X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sw01 ∷ X1 ∷ Sb4-2-13-0 ∷ X1 ∷ Sb4-2-13-0 ∷ Sw12 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ Sb2-4-01-3 ∷ K1 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ [])
  (rw 123 (q1 c4) ∷
   rw⁻ 125 (q2 c4) ∷
   rw 124 (q3 c4) ∷
   rw⁻ 126 (q4 c4) ∷
   rw⁻ 125 (q4 c4) ∷
   re 126 3 (CS02 ∷ []) ∷
   rw⁻ 127 (q5 c4) ∷
   rw 126 (q6 c4) ∷
   rw⁻ 127 (q7 c4) ∷
   rw 126 (q8 c4) ∷
   rw 127 (q9 c4) ∷
   rw 128 (q8 c4) ∷
   rw 129 (q9 c4) ∷
   rw 130 (q5 c4) ∷
   rw 125 (q10 c4) ∷
   rw 126 (q11 c4) ∷
   rw 127 (q10 c4) ∷
   rw 128 (q11 c4) ∷
   rw 129 (q4 c4) ∷
   rw 124 (q12 c4) ∷
   rw 125 (q13 c4) ∷
   rw 126 (q12 c4) ∷
   rw 127 (q13 c4) ∷
   rw 128 (q2 c4) ∷
   rw 123 (q14 c4) ∷
   rw 124 (q15 c4) ∷
   rw 125 (q14 c4) ∷
   rw 126 (q15 c4) ∷
   rw 127 (q16 c4) ∷
   rw 122 (q17 c4) ∷
   rw 123 (q18 c4) ∷
   rw 124 (q17 c4) ∷
   rw 125 (q18 c4) ∷
   rw 126 (q2 c4) ∷
   rw 121 (q19 c4) ∷
   rw 122 (q20 c4) ∷
   rw 123 (q19 c4) ∷
   rw 124 (q20 c4) ∷
   rw 125 (q4 c4) ∷
   rw 120 (q21 c4) ∷
   rw 121 (q22 c4) ∷
   rw 122 (q21 c4) ∷
   rw 123 (q22 c4) ∷
   rw 124 (q5 c4) ∷
   rw⁻ 119 (q23 c4) ∷
   rw⁻ 118 (q24 c4) ∷
   rw⁻ 117 (q25 c4) ∷
   rw⁻ 116 (q25 c4) ∷
   rw⁻ 115 (q24 c4) ∷
   rw⁻ 114 (q23 c4) ∷
   rw⁻ 113 (q26 c4) ∷
   rw⁻ 112 (q25 c4) ∷
   rw⁻ 111 (q25 c4) ∷
   rw⁻ 110 (q26 c4) ∷
   rw⁻ 109 (q23 c4) ∷
   rw⁻ 108 (q24 c4) ∷
   rw⁻ 107 (q25 c4) ∷
   rw⁻ 106 (q25 c4) ∷
   rw⁻ 105 (q24 c4) ∷
   rw⁻ 104 (q23 c4) ∷
   rw⁻ 103 (q26 c4) ∷
   rw⁻ 102 (q27 c4) ∷
   rw⁻ 101 (q27 c4) ∷
   rw⁻ 100 (q26 c4) ∷
   rw⁻ 99 (q25 c4) ∷
   rw⁻ 98 (q25 c4) ∷
   rw⁻ 97 (q25 c4) ∷
   rw⁻ 96 (q23 c4) ∷
   rw⁻ 95 (q26 c4) ∷
   rw⁻ 94 (q27 c4) ∷
   rw⁻ 93 (q27 c4) ∷
   rw⁻ 92 (q26 c4) ∷
   rw⁻ 91 (q25 c4) ∷
   rw⁻ 90 (q28 c4) ∷
   rw 124 (q29 c4) ∷
   rw⁻ 123 (q30 c4) ∷
   rw⁻ 122 (q31 c4) ∷
   rw⁻ 121 (q32 c4) ∷
   rw⁻ 120 (q33 c4) ∷
   rw⁻ 119 (q33 c4) ∷
   rw⁻ 118 (q32 c4) ∷
   rw⁻ 117 (q31 c4) ∷
   rw⁻ 116 (q34 c4) ∷
   rw⁻ 115 (q33 c4) ∷
   rw⁻ 114 (q33 c4) ∷
   rw⁻ 113 (q34 c4) ∷
   rw⁻ 112 (q31 c4) ∷
   rw⁻ 111 (q32 c4) ∷
   rw⁻ 110 (q33 c4) ∷
   rw⁻ 109 (q33 c4) ∷
   rw⁻ 108 (q32 c4) ∷
   rw⁻ 107 (q31 c4) ∷
   rw⁻ 106 (q34 c4) ∷
   rw⁻ 105 (q30 c4) ∷
   rw⁻ 104 (q30 c4) ∷
   rw⁻ 103 (q34 c4) ∷
   rw⁻ 102 (q33 c4) ∷
   rw⁻ 101 (q33 c4) ∷
   rw⁻ 100 (q33 c4) ∷
   rw⁻ 99 (q31 c4) ∷
   rw⁻ 98 (q34 c4) ∷
   rw⁻ 97 (q30 c4) ∷
   rw⁻ 96 (q30 c4) ∷
   rw⁻ 95 (q34 c4) ∷
   rw⁻ 94 (q33 c4) ∷
   rw⁻ 93 (q35 c4) ∷
   rw⁻ 129 (q5 c4) ∷
   rw⁻ 128 (q36 c4) ∷
   rw⁻ 130 (q4 c4) ∷
   rw 129 (q37 c4) ∷
   rw⁻ 131 (q2 c4) ∷
   re 130 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 132 (q2 c4) ∷
   rw⁻ 132 (q16 c4) ∷
   rw 131 (q38 c4) ∷
   rw⁻ 133 (q2 c4) ∷
   rw⁻ 132 (q2 c4) ∷
   re 133 3 (CS13 ∷ []) ∷
   rw⁻ 134 (q4 c4) ∷
   rw 133 (q39 c4) ∷
   rw⁻ 135 (q5 c4) ∷
   rw⁻ 134 (q36 c4) ∷
   rw⁻ 135 (q40 c4) ∷
   rw 134 (q8 c4) ∷
   rw 135 (q41 c4) ∷
   rw 136 (q8 c4) ∷
   rw 137 (q41 c4) ∷
   rw 138 (q5 c4) ∷
   rw 133 (q10 c4) ∷
   rw 134 (q42 c4) ∷
   rw 135 (q10 c4) ∷
   rw 136 (q42 c4) ∷
   rw 137 (q4 c4) ∷
   rw 132 (q12 c4) ∷
   rw 133 (q43 c4) ∷
   rw 134 (q12 c4) ∷
   rw 135 (q43 c4) ∷
   rw 136 (q2 c4) ∷
   rw 131 (q14 c4) ∷
   rw 132 (q44 c4) ∷
   rw 133 (q14 c4) ∷
   rw 134 (q44 c4) ∷
   rw 135 (q16 c4) ∷
   rw 130 (q17 c4) ∷
   rw 131 (q45 c4) ∷
   rw 132 (q17 c4) ∷
   rw 133 (q45 c4) ∷
   rw 134 (q2 c4) ∷
   rw 129 (q19 c4) ∷
   rw 130 (q46 c4) ∷
   rw 131 (q19 c4) ∷
   rw 132 (q46 c4) ∷ []) Eq.refl

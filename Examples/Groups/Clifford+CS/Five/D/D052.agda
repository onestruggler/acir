{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD052 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D052 (Sᴰ : SD052) where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)

-- The lemmas of other derivation modules (DSig).
private
  lem-comm-push-CS04-sw0-L : Ws → St 1620
  lem-comm-push-CS04-sw0-L = pickᴰ 0 Sᴰ
  lem-comm-push-CS04-sw1-L : Ws → St 1621
  lem-comm-push-CS04-sw1-L = pickᴰ 1 Sᴰ
  lem-comm-push-CS14-sw0-L : Ws → St 1622
  lem-comm-push-CS14-sw0-L = pickᴰ 2 Sᴰ
  lem-comm-push-SBOX⟨1·4·20·3⟩-sw1-R : Ws → St 1623
  lem-comm-push-SBOX⟨1·4·20·3⟩-sw1-R = pickᴰ 3 Sᴰ
  lem-comm-push-SBOX⟨0·2·43·1⟩-sw2-R : Ws → St 1624
  lem-comm-push-SBOX⟨0·2·43·1⟩-sw2-R = pickᴰ 4 Sᴰ
  lem-comm-push-SBOX⟨0·4·32·1⟩-sw1-R : Ws → St 1625
  lem-comm-push-SBOX⟨0·4·32·1⟩-sw1-R = pickᴰ 5 Sᴰ
  lem-comm-push-SBOX⟨0·3·42·1⟩-sw3-R : Ws → St 1626
  lem-comm-push-SBOX⟨0·3·42·1⟩-sw3-R = pickᴰ 6 Sᴰ
  lem-comm-push-SBOX⟨0·4·21·3⟩-sw0-R : Ws → St 1627
  lem-comm-push-SBOX⟨0·4·21·3⟩-sw0-R = pickᴰ 7 Sᴰ
  lem-comm-push-SBOX⟨0·4·31·2⟩-sw2-R : Ws → St 1628
  lem-comm-push-SBOX⟨0·4·31·2⟩-sw2-R = pickᴰ 8 Sᴰ
  lem-comm-push-SBOX⟨2·4·10·3⟩-sw0-R : Ws → St 1629
  lem-comm-push-SBOX⟨2·4·10·3⟩-sw0-R = pickᴰ 9 Sᴰ
  lem-F4-I-K3-at0213243140 : Ws → St 1630
  lem-F4-I-K3-at0213243140 = pickᴰ 10 Sᴰ
  lem-F4-I-S2-at0213243140 : Ws → St 1631
  lem-F4-I-S2-at0213243140 = pickᴰ 11 Sᴰ
  lem-F4-K3-I-at0213243140 : Ws → St 1632
  lem-F4-K3-I-at0213243140 = pickᴰ 12 Sᴰ
  lem-F4-K3-K3-at0213243140 : Ws → St 1633
  lem-F4-K3-K3-at0213243140 = pickᴰ 13 Sᴰ
  lem-F4-K3-S2-at0213243140 : Ws → St 1634
  lem-F4-K3-S2-at0213243140 = pickᴰ 14 Sᴰ
  lem-F4-S2-I-at0213243140 : Ws → St 1635
  lem-F4-S2-I-at0213243140 = pickᴰ 15 Sᴰ
  lem-F4-S2-K3-at0213243140 : Ws → St 1636
  lem-F4-S2-K3-at0213243140 = pickᴰ 16 Sᴰ
  lem-F4-S2-S2-at0213243140 : Ws → St 1637
  lem-F4-S2-S2-at0213243140 = pickᴰ 17 Sᴰ
  lem-F4-I-CS2-at0213243140 : Ws → St 1638
  lem-F4-I-CS2-at0213243140 = pickᴰ 18 Sᴰ
  lem-F4-S2-CS2-at0213243140 : Ws → St 1639
  lem-F4-S2-CS2-at0213243140 = pickᴰ 19 Sᴰ
  lem-F4-CS2-CS2-at0213243140 : Ws → St 1640
  lem-F4-CS2-CS2-at0213243140 = pickᴰ 20 Sᴰ
  lem-F4-CS2-I-at0213243140 : Ws → St 1641
  lem-F4-CS2-I-at0213243140 = pickᴰ 21 Sᴰ
  lem-F4-CS2-S2-at0213243140 : Ws → St 1642
  lem-F4-CS2-S2-at0213243140 = pickᴰ 22 Sᴰ
  lem-F5-23 : Ws → St 1590
  lem-F5-23 = pickᴰ 23 Sᴰ
  lem-F4-CS2-K3-at0213243140 : Ws → St 1643
  lem-F4-CS2-K3-at0213243140 = pickᴰ 24 Sᴰ
  lem-F4-K3-CS2-at0213243140 : Ws → St 1644
  lem-F4-K3-CS2-at0213243140 = pickᴰ 25 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = wlE 18 (lit c4)
  q2 : Ws → Eqn
  q2 c4 = sE 1622 (lem-comm-push-CS14-sw0-L c4)
  q3 : Ws → Eqn
  q3 c4 = wlE 6 (lit c4)
  q4 : Ws → Eqn
  q4 c4 = sE 1621 (lem-comm-push-CS04-sw1-L c4)
  q5 : Ws → Eqn
  q5 c4 = sE 1620 (lem-comm-push-CS04-sw0-L c4)
  q6 : Ws → Eqn
  q6 c4 = wlE 3 (lit c4)
  q7 : Ws → Eqn
  q7 c4 = wlE 17 (lit c4)
  q8 : Ws → Eqn
  q8 c4 = wlE 13 (lit c4)
  q9 : Ws → Eqn
  q9 c4 = wlE 4 (lit c4)
  q10 : Ws → Eqn
  q10 c4 = wlE 1455 (lit c4)
  q11 : Ws → Eqn
  q11 c4 = sE 1590 (lem-F5-23 c4)
  q12 : Ws → Eqn
  q12 c4 = eqn (Sw23 ∷ X4 ∷ []) (X4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (X))
  q13 : Ws → Eqn
  q13 c4 = sE 1624 (lem-comm-push-SBOX⟨0·2·43·1⟩-sw2-R c4)
  q14 : Ws → Eqn
  q14 c4 = wlE 1456 (lit c4)
  q15 : Ws → Eqn
  q15 c4 = sE 1626 (lem-comm-push-SBOX⟨0·3·42·1⟩-sw3-R c4)
  q16 : Ws → Eqn
  q16 c4 = eqn (Sw12 ∷ X3 ∷ []) (X3 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (X))
  q17 : Ws → Eqn
  q17 c4 = sE 1625 (lem-comm-push-SBOX⟨0·4·32·1⟩-sw1-R c4)
  q18 : Ws → Eqn
  q18 c4 = wlE 1457 (lit c4)
  q19 : Ws → Eqn
  q19 c4 = sE 1628 (lem-comm-push-SBOX⟨0·4·31·2⟩-sw2-R c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (c₂ (Swap) (X))
  q21 : Ws → Eqn
  q21 c4 = sE 1627 (lem-comm-push-SBOX⟨0·4·21·3⟩-sw0-R c4)
  q22 : Ws → Eqn
  q22 c4 = wlE 1458 (lit c4)
  q23 : Ws → Eqn
  q23 c4 = sE 1623 (lem-comm-push-SBOX⟨1·4·20·3⟩-sw1-R c4)
  q24 : Ws → Eqn
  q24 c4 = wlE 1459 (lit c4)
  q25 : Ws → Eqn
  q25 c4 = sE 1629 (lem-comm-push-SBOX⟨2·4·10·3⟩-sw0-R c4)
  q26 : Ws → Eqn
  q26 c4 = wlE 1460 (lit c4)
  q27 : Ws → Eqn
  q27 c4 = sE 1644 (lem-F4-K3-CS2-at0213243140 c4)
  q28 : Ws → Eqn
  q28 c4 = sE 1643 (lem-F4-CS2-K3-at0213243140 c4)
  q29 : Ws → Eqn
  q29 c4 = sE 1640 (lem-F4-CS2-CS2-at0213243140 c4)
  q30 : Ws → Eqn
  q30 c4 = sE 1633 (lem-F4-K3-K3-at0213243140 c4)
  q31 : Ws → Eqn
  q31 c4 = wpE 1306 c4
  q32 : Ws → Eqn
  q32 c4 = sE 1639 (lem-F4-S2-CS2-at0213243140 c4)
  q33 : Ws → Eqn
  q33 c4 = sE 1636 (lem-F4-S2-K3-at0213243140 c4)
  q34 : Ws → Eqn
  q34 c4 = sE 1637 (lem-F4-S2-S2-at0213243140 c4)
  q35 : Ws → Eqn
  q35 c4 = wlE 1461 (lit c4)
  q36 : Ws → Eqn
  q36 c4 = sE 1631 (lem-F4-I-S2-at0213243140 c4)
  q37 : Ws → Eqn
  q37 c4 = sE 1638 (lem-F4-I-CS2-at0213243140 c4)
  q38 : Ws → Eqn
  q38 c4 = sE 1630 (lem-F4-I-K3-at0213243140 c4)
  q39 : Ws → Eqn
  q39 c4 = sE 1635 (lem-F4-S2-I-at0213243140 c4)
  q40 : Ws → Eqn
  q40 c4 = sE 1642 (lem-F4-CS2-S2-at0213243140 c4)
  q41 : Ws → Eqn
  q41 c4 = sE 1641 (lem-F4-CS2-I-at0213243140 c4)
  q42 : Ws → Eqn
  q42 c4 = sE 1634 (lem-F4-K3-S2-at0213243140 c4)
  q43 : Ws → Eqn
  q43 c4 = sE 1632 (lem-F4-K3-I-at0213243140 c4)

-- deb-CKS-split-a @0213243140 part0: 500 steps
lem-deb-CKS-split-a-at0213243140-part0 : Ws → ⟪ (CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ X3 ∷ Sb0-4-31-2 ∷ X3 ∷ Sb0-4-31-2 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) ⟫ʷ
lem-deb-CKS-split-a-at0213243140-part0 c4 = derive (CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ X3 ∷ Sb0-4-31-2 ∷ X3 ∷ Sb0-4-31-2 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ [])
  (rw⁻ 1 (q1 c4) ∷
   rw 0 (q2 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   rw 1 (q4 c4) ∷
   rw⁻ 3 (q1 c4) ∷
   rw 2 (q5 c4) ∷
   rw⁻ 4 (q6 c4) ∷
   rw 3 (q7 c4) ∷
   rw⁻ 5 (q3 c4) ∷
   rw 4 (q8 c4) ∷
   rw⁻ 6 (q9 c4) ∷
   re 5 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 7 (q9 c4) ∷
   rw⁻ 7 (q6 c4) ∷
   rw 6 (q10 c4) ∷
   rw⁻ 7 (q11 c4) ∷
   rw 6 (q12 c4) ∷
   rw 7 (q13 c4) ∷
   rw 8 (q12 c4) ∷
   rw 9 (q13 c4) ∷
   rw 10 (q6 c4) ∷
   rw 5 (q14 c4) ∷
   rw 6 (q15 c4) ∷
   rw 7 (q14 c4) ∷
   rw 8 (q15 c4) ∷
   rw 9 (q9 c4) ∷
   rw 4 (q16 c4) ∷
   rw 5 (q17 c4) ∷
   rw 6 (q16 c4) ∷
   rw 7 (q17 c4) ∷
   rw 8 (q3 c4) ∷
   rw 3 (q18 c4) ∷
   rw 4 (q19 c4) ∷
   rw 5 (q18 c4) ∷
   rw 6 (q19 c4) ∷
   rw 7 (q6 c4) ∷
   rw 2 (q20 c4) ∷
   rw 3 (q21 c4) ∷
   rw 4 (q20 c4) ∷
   rw 5 (q21 c4) ∷
   rw 6 (q1 c4) ∷
   rw 1 (q22 c4) ∷
   rw 2 (q23 c4) ∷
   rw 3 (q22 c4) ∷
   rw 4 (q23 c4) ∷
   rw 5 (q3 c4) ∷
   rw 0 (q24 c4) ∷
   rw 1 (q25 c4) ∷
   rw 2 (q24 c4) ∷
   rw 3 (q25 c4) ∷
   rw 4 (q1 c4) ∷
   rw 4 (q26 c4) ∷
   rw⁻ 3 (q27 c4) ∷
   rw⁻ 9 (q1 c4) ∷
   rw 8 (q2 c4) ∷
   rw⁻ 10 (q3 c4) ∷
   rw 9 (q4 c4) ∷
   rw⁻ 11 (q1 c4) ∷
   rw 10 (q5 c4) ∷
   rw⁻ 12 (q6 c4) ∷
   rw 11 (q7 c4) ∷
   rw⁻ 13 (q3 c4) ∷
   rw 12 (q8 c4) ∷
   rw⁻ 14 (q9 c4) ∷
   re 13 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 15 (q9 c4) ∷
   rw⁻ 15 (q6 c4) ∷
   rw 14 (q10 c4) ∷
   rw⁻ 15 (q11 c4) ∷
   rw 14 (q12 c4) ∷
   rw 15 (q13 c4) ∷
   rw 16 (q12 c4) ∷
   rw 17 (q13 c4) ∷
   rw 18 (q6 c4) ∷
   rw 13 (q14 c4) ∷
   rw 14 (q15 c4) ∷
   rw 15 (q14 c4) ∷
   rw 16 (q15 c4) ∷
   rw 17 (q9 c4) ∷
   rw 12 (q16 c4) ∷
   rw 13 (q17 c4) ∷
   rw 14 (q16 c4) ∷
   rw 15 (q17 c4) ∷
   rw 16 (q3 c4) ∷
   rw 11 (q18 c4) ∷
   rw 12 (q19 c4) ∷
   rw 13 (q18 c4) ∷
   rw 14 (q19 c4) ∷
   rw 15 (q6 c4) ∷
   rw 10 (q20 c4) ∷
   rw 11 (q21 c4) ∷
   rw 12 (q20 c4) ∷
   rw 13 (q21 c4) ∷
   rw 14 (q1 c4) ∷
   rw 9 (q22 c4) ∷
   rw 10 (q23 c4) ∷
   rw 11 (q22 c4) ∷
   rw 12 (q23 c4) ∷
   rw 13 (q3 c4) ∷
   rw 8 (q24 c4) ∷
   rw 9 (q25 c4) ∷
   rw 10 (q24 c4) ∷
   rw 11 (q25 c4) ∷
   rw 12 (q1 c4) ∷
   rw⁻ 7 (q28 c4) ∷
   rw⁻ 6 (q29 c4) ∷
   rw 12 (q26 c4) ∷
   rw⁻ 11 (q27 c4) ∷
   rw⁻ 10 (q30 c4) ∷
   rw⁻ 9 (q27 c4) ∷
   rw⁻ 17 (q1 c4) ∷
   rw 16 (q2 c4) ∷
   rw⁻ 18 (q3 c4) ∷
   rw 17 (q4 c4) ∷
   rw⁻ 19 (q1 c4) ∷
   rw 18 (q5 c4) ∷
   rw⁻ 20 (q6 c4) ∷
   rw 19 (q7 c4) ∷
   rw⁻ 21 (q3 c4) ∷
   rw 20 (q8 c4) ∷
   rw⁻ 22 (q9 c4) ∷
   re 21 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 23 (q9 c4) ∷
   rw⁻ 23 (q6 c4) ∷
   rw 22 (q10 c4) ∷
   rw⁻ 23 (q11 c4) ∷
   rw 22 (q12 c4) ∷
   rw 23 (q13 c4) ∷
   rw 24 (q12 c4) ∷
   rw 25 (q13 c4) ∷
   rw 26 (q6 c4) ∷
   rw 21 (q14 c4) ∷
   rw 22 (q15 c4) ∷
   rw 23 (q14 c4) ∷
   rw 24 (q15 c4) ∷
   rw 25 (q9 c4) ∷
   rw 20 (q16 c4) ∷
   rw 21 (q17 c4) ∷
   rw 22 (q16 c4) ∷
   rw 23 (q17 c4) ∷
   rw 24 (q3 c4) ∷
   rw 19 (q18 c4) ∷
   rw 20 (q19 c4) ∷
   rw 21 (q18 c4) ∷
   rw 22 (q19 c4) ∷
   rw 23 (q6 c4) ∷
   rw 18 (q20 c4) ∷
   rw 19 (q21 c4) ∷
   rw 20 (q20 c4) ∷
   rw 21 (q21 c4) ∷
   rw 22 (q1 c4) ∷
   rw 17 (q22 c4) ∷
   rw 18 (q23 c4) ∷
   rw 19 (q22 c4) ∷
   rw 20 (q23 c4) ∷
   rw 21 (q3 c4) ∷
   rw 16 (q24 c4) ∷
   rw 17 (q25 c4) ∷
   rw 18 (q24 c4) ∷
   rw 19 (q25 c4) ∷
   rw 20 (q1 c4) ∷
   rw⁻ 15 (q28 c4) ∷
   rw⁻ 14 (q29 c4) ∷
   rw⁻ 13 (q28 c4) ∷
   rw⁻ 12 (q29 c4) ∷
   rw 20 (q31 c4) ∷
   rw⁻ 19 (q32 c4) ∷
   rw⁻ 18 (q33 c4) ∷
   rw⁻ 17 (q32 c4) ∷
   rw⁻ 16 (q33 c4) ∷
   rw⁻ 15 (q32 c4) ∷
   rw 24 (q31 c4) ∷
   rw⁻ 23 (q34 c4) ∷
   rw⁻ 22 (q32 c4) ∷
   rw⁻ 21 (q33 c4) ∷
   rw⁻ 20 (q32 c4) ∷
   rw⁻ 19 (q33 c4) ∷
   rw⁻ 18 (q32 c4) ∷
   rw 28 (q31 c4) ∷
   rw⁻ 27 (q34 c4) ∷
   rw⁻ 26 (q34 c4) ∷
   rw⁻ 25 (q32 c4) ∷
   rw⁻ 24 (q33 c4) ∷
   rw⁻ 23 (q32 c4) ∷
   rw⁻ 22 (q33 c4) ∷
   rw⁻ 21 (q32 c4) ∷
   rw⁻ 32 (q35 c4) ∷
   rw⁻ 31 (q36 c4) ∷
   rw⁻ 30 (q36 c4) ∷
   rw⁻ 29 (q36 c4) ∷
   rw⁻ 28 (q37 c4) ∷
   rw⁻ 27 (q38 c4) ∷
   rw⁻ 26 (q37 c4) ∷
   rw⁻ 25 (q38 c4) ∷
   rw⁻ 24 (q37 c4) ∷
   rw 36 (q31 c4) ∷
   rw⁻ 35 (q39 c4) ∷
   rw⁻ 34 (q34 c4) ∷
   rw⁻ 33 (q34 c4) ∷
   rw⁻ 32 (q34 c4) ∷
   rw⁻ 31 (q32 c4) ∷
   rw⁻ 30 (q33 c4) ∷
   rw⁻ 29 (q32 c4) ∷
   rw⁻ 28 (q33 c4) ∷
   rw⁻ 27 (q32 c4) ∷
   rw⁻ 41 (q1 c4) ∷
   rw 40 (q2 c4) ∷
   rw⁻ 42 (q3 c4) ∷
   rw 41 (q4 c4) ∷
   rw⁻ 43 (q1 c4) ∷
   rw 42 (q5 c4) ∷
   rw⁻ 44 (q6 c4) ∷
   rw 43 (q7 c4) ∷
   rw⁻ 45 (q3 c4) ∷
   rw 44 (q8 c4) ∷
   rw⁻ 46 (q9 c4) ∷
   re 45 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 47 (q9 c4) ∷
   rw⁻ 47 (q6 c4) ∷
   rw 46 (q10 c4) ∷
   rw⁻ 47 (q11 c4) ∷
   rw 46 (q12 c4) ∷
   rw 47 (q13 c4) ∷
   rw 48 (q12 c4) ∷
   rw 49 (q13 c4) ∷
   rw 50 (q6 c4) ∷
   rw 45 (q14 c4) ∷
   rw 46 (q15 c4) ∷
   rw 47 (q14 c4) ∷
   rw 48 (q15 c4) ∷
   rw 49 (q9 c4) ∷
   rw 44 (q16 c4) ∷
   rw 45 (q17 c4) ∷
   rw 46 (q16 c4) ∷
   rw 47 (q17 c4) ∷
   rw 48 (q3 c4) ∷
   rw 43 (q18 c4) ∷
   rw 44 (q19 c4) ∷
   rw 45 (q18 c4) ∷
   rw 46 (q19 c4) ∷
   rw 47 (q6 c4) ∷
   rw 42 (q20 c4) ∷
   rw 43 (q21 c4) ∷
   rw 44 (q20 c4) ∷
   rw 45 (q21 c4) ∷
   rw 46 (q1 c4) ∷
   rw 41 (q22 c4) ∷
   rw 42 (q23 c4) ∷
   rw 43 (q22 c4) ∷
   rw 44 (q23 c4) ∷
   rw 45 (q3 c4) ∷
   rw 40 (q24 c4) ∷
   rw 41 (q25 c4) ∷
   rw 42 (q24 c4) ∷
   rw 43 (q25 c4) ∷
   rw 44 (q1 c4) ∷
   rw⁻ 39 (q40 c4) ∷
   rw⁻ 38 (q41 c4) ∷
   rw⁻ 37 (q40 c4) ∷
   rw⁻ 36 (q40 c4) ∷
   rw⁻ 35 (q40 c4) ∷
   rw⁻ 34 (q29 c4) ∷
   rw⁻ 33 (q28 c4) ∷
   rw⁻ 32 (q29 c4) ∷
   rw⁻ 31 (q28 c4) ∷
   rw⁻ 30 (q29 c4) ∷
   rw⁻ 45 (q1 c4) ∷
   rw 44 (q2 c4) ∷
   rw⁻ 46 (q3 c4) ∷
   rw 45 (q4 c4) ∷
   rw⁻ 47 (q1 c4) ∷
   rw 46 (q5 c4) ∷
   rw⁻ 48 (q6 c4) ∷
   rw 47 (q7 c4) ∷
   rw⁻ 49 (q3 c4) ∷
   rw 48 (q8 c4) ∷
   rw⁻ 50 (q9 c4) ∷
   re 49 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 51 (q9 c4) ∷
   rw⁻ 51 (q6 c4) ∷
   rw 50 (q10 c4) ∷
   rw⁻ 51 (q11 c4) ∷
   rw 50 (q12 c4) ∷
   rw 51 (q13 c4) ∷
   rw 52 (q12 c4) ∷
   rw 53 (q13 c4) ∷
   rw 54 (q6 c4) ∷
   rw 49 (q14 c4) ∷
   rw 50 (q15 c4) ∷
   rw 51 (q14 c4) ∷
   rw 52 (q15 c4) ∷
   rw 53 (q9 c4) ∷
   rw 48 (q16 c4) ∷
   rw 49 (q17 c4) ∷
   rw 50 (q16 c4) ∷
   rw 51 (q17 c4) ∷
   rw 52 (q3 c4) ∷
   rw 47 (q18 c4) ∷
   rw 48 (q19 c4) ∷
   rw 49 (q18 c4) ∷
   rw 50 (q19 c4) ∷
   rw 51 (q6 c4) ∷
   rw 46 (q20 c4) ∷
   rw 47 (q21 c4) ∷
   rw 48 (q20 c4) ∷
   rw 49 (q21 c4) ∷
   rw 50 (q1 c4) ∷
   rw 45 (q22 c4) ∷
   rw 46 (q23 c4) ∷
   rw 47 (q22 c4) ∷
   rw 48 (q23 c4) ∷
   rw 49 (q3 c4) ∷
   rw 44 (q24 c4) ∷
   rw 45 (q25 c4) ∷
   rw 46 (q24 c4) ∷
   rw 47 (q25 c4) ∷
   rw 48 (q1 c4) ∷
   rw⁻ 43 (q29 c4) ∷
   rw⁻ 42 (q40 c4) ∷
   rw⁻ 41 (q41 c4) ∷
   rw⁻ 40 (q40 c4) ∷
   rw⁻ 39 (q40 c4) ∷
   rw⁻ 38 (q40 c4) ∷
   rw⁻ 37 (q29 c4) ∷
   rw⁻ 36 (q28 c4) ∷
   rw⁻ 35 (q29 c4) ∷
   rw⁻ 34 (q28 c4) ∷
   rw⁻ 33 (q29 c4) ∷
   rw⁻ 49 (q1 c4) ∷
   rw 48 (q2 c4) ∷
   rw⁻ 50 (q3 c4) ∷
   rw 49 (q4 c4) ∷
   rw⁻ 51 (q1 c4) ∷
   rw 50 (q5 c4) ∷
   rw⁻ 52 (q6 c4) ∷
   rw 51 (q7 c4) ∷
   rw⁻ 53 (q3 c4) ∷
   rw 52 (q8 c4) ∷
   rw⁻ 54 (q9 c4) ∷
   re 53 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 55 (q9 c4) ∷
   rw⁻ 55 (q6 c4) ∷
   rw 54 (q10 c4) ∷
   rw⁻ 55 (q11 c4) ∷
   rw 54 (q12 c4) ∷
   rw 55 (q13 c4) ∷
   rw 56 (q12 c4) ∷
   rw 57 (q13 c4) ∷
   rw 58 (q6 c4) ∷
   rw 53 (q14 c4) ∷
   rw 54 (q15 c4) ∷
   rw 55 (q14 c4) ∷
   rw 56 (q15 c4) ∷
   rw 57 (q9 c4) ∷
   rw 52 (q16 c4) ∷
   rw 53 (q17 c4) ∷
   rw 54 (q16 c4) ∷
   rw 55 (q17 c4) ∷
   rw 56 (q3 c4) ∷
   rw 51 (q18 c4) ∷
   rw 52 (q19 c4) ∷
   rw 53 (q18 c4) ∷
   rw 54 (q19 c4) ∷
   rw 55 (q6 c4) ∷
   rw 50 (q20 c4) ∷
   rw 51 (q21 c4) ∷
   rw 52 (q20 c4) ∷
   rw 53 (q21 c4) ∷
   rw 54 (q1 c4) ∷
   rw 49 (q22 c4) ∷
   rw 50 (q23 c4) ∷
   rw 51 (q22 c4) ∷
   rw 52 (q23 c4) ∷
   rw 53 (q3 c4) ∷
   rw 48 (q24 c4) ∷
   rw 49 (q25 c4) ∷
   rw 50 (q24 c4) ∷
   rw 51 (q25 c4) ∷
   rw 52 (q1 c4) ∷
   rw⁻ 47 (q29 c4) ∷
   rw⁻ 46 (q29 c4) ∷
   rw⁻ 45 (q40 c4) ∷
   rw⁻ 44 (q41 c4) ∷
   rw⁻ 43 (q40 c4) ∷
   rw⁻ 42 (q40 c4) ∷
   rw⁻ 41 (q40 c4) ∷
   rw⁻ 40 (q29 c4) ∷
   rw⁻ 39 (q28 c4) ∷
   rw⁻ 38 (q29 c4) ∷
   rw⁻ 37 (q28 c4) ∷
   rw⁻ 36 (q29 c4) ∷
   rw⁻ 53 (q1 c4) ∷
   rw 52 (q2 c4) ∷
   rw⁻ 54 (q3 c4) ∷
   rw 53 (q4 c4) ∷
   rw⁻ 55 (q1 c4) ∷
   rw 54 (q5 c4) ∷
   rw⁻ 56 (q6 c4) ∷
   rw 55 (q7 c4) ∷
   rw⁻ 57 (q3 c4) ∷
   rw 56 (q8 c4) ∷
   rw⁻ 58 (q9 c4) ∷
   re 57 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 59 (q9 c4) ∷
   rw⁻ 59 (q6 c4) ∷
   rw 58 (q10 c4) ∷
   rw⁻ 59 (q11 c4) ∷
   rw 58 (q12 c4) ∷
   rw 59 (q13 c4) ∷
   rw 60 (q12 c4) ∷
   rw 61 (q13 c4) ∷
   rw 62 (q6 c4) ∷
   rw 57 (q14 c4) ∷
   rw 58 (q15 c4) ∷
   rw 59 (q14 c4) ∷
   rw 60 (q15 c4) ∷
   rw 61 (q9 c4) ∷
   rw 56 (q16 c4) ∷
   rw 57 (q17 c4) ∷
   rw 58 (q16 c4) ∷
   rw 59 (q17 c4) ∷
   rw 60 (q3 c4) ∷
   rw 55 (q18 c4) ∷
   rw 56 (q19 c4) ∷
   rw 57 (q18 c4) ∷
   rw 58 (q19 c4) ∷
   rw 59 (q6 c4) ∷
   rw 54 (q20 c4) ∷
   rw 55 (q21 c4) ∷
   rw 56 (q20 c4) ∷
   rw 57 (q21 c4) ∷
   rw 58 (q1 c4) ∷
   rw 53 (q22 c4) ∷
   rw 54 (q23 c4) ∷
   rw 55 (q22 c4) ∷
   rw 56 (q23 c4) ∷
   rw 57 (q3 c4) ∷
   rw 52 (q24 c4) ∷
   rw 53 (q25 c4) ∷
   rw 54 (q24 c4) ∷
   rw 55 (q25 c4) ∷
   rw 56 (q1 c4) ∷
   rw⁻ 51 (q29 c4) ∷
   rw⁻ 50 (q29 c4) ∷
   rw⁻ 49 (q29 c4) ∷
   rw⁻ 48 (q40 c4) ∷
   rw⁻ 47 (q41 c4) ∷
   rw⁻ 46 (q40 c4) ∷
   rw⁻ 45 (q40 c4) ∷
   rw⁻ 44 (q40 c4) ∷
   rw⁻ 43 (q29 c4) ∷
   rw⁻ 42 (q28 c4) ∷
   rw⁻ 41 (q29 c4) ∷
   rw⁻ 40 (q28 c4) ∷
   rw⁻ 39 (q29 c4) ∷
   rw 56 (q26 c4) ∷
   rw⁻ 55 (q27 c4) ∷
   rw⁻ 54 (q27 c4) ∷
   rw⁻ 53 (q27 c4) ∷
   rw⁻ 52 (q27 c4) ∷
   rw⁻ 51 (q42 c4) ∷
   rw⁻ 50 (q43 c4) ∷
   rw⁻ 49 (q42 c4) ∷
   rw⁻ 48 (q42 c4) ∷
   rw⁻ 47 (q42 c4) ∷
   rw⁻ 46 (q27 c4) ∷
   rw⁻ 45 (q30 c4) ∷
   rw⁻ 44 (q27 c4) ∷
   rw⁻ 43 (q30 c4) ∷
   rw⁻ 42 (q27 c4) ∷
   rw⁻ 61 (q1 c4) ∷
   rw 60 (q2 c4) ∷
   rw⁻ 62 (q3 c4) ∷
   rw 61 (q4 c4) ∷
   rw⁻ 63 (q1 c4) ∷
   rw 62 (q5 c4) ∷
   rw⁻ 64 (q6 c4) ∷
   rw 63 (q7 c4) ∷
   rw⁻ 65 (q3 c4) ∷
   rw 64 (q8 c4) ∷
   rw⁻ 66 (q9 c4) ∷
   re 65 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 67 (q9 c4) ∷
   rw⁻ 67 (q6 c4) ∷
   rw 66 (q10 c4) ∷
   rw⁻ 67 (q11 c4) ∷
   rw 66 (q12 c4) ∷
   rw 67 (q13 c4) ∷
   rw 68 (q12 c4) ∷
   rw 69 (q13 c4) ∷
   rw 70 (q6 c4) ∷
   rw 65 (q14 c4) ∷
   rw 66 (q15 c4) ∷
   rw 67 (q14 c4) ∷
   rw 68 (q15 c4) ∷
   rw 69 (q9 c4) ∷
   rw 64 (q16 c4) ∷
   rw 65 (q17 c4) ∷
   rw 66 (q16 c4) ∷
   rw 67 (q17 c4) ∷ []) Eq.refl

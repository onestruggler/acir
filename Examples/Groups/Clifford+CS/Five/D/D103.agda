{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D103 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0003 ; wl0004 ; wl0006 ; wl0018 ; wl0024 ; wl0046 ; wl0047 ; wl0146 ; wl1456 ; wl1457 ; wl1458 ; wl1459 ; wl1460 ; wl1461 ; wl1715)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-F4-I-K1-at0440 ; lem-F4-I-K2-at0440 ; lem-F4-K2-K1-at0440 ; lem-F4-K2-K2-at0440)
open import Examples.Groups.Clifford+CS.Five.D.D017 using (lem-F4-CS1-CS1-at0440 ; lem-F4-CS1-K1-at0440 ; lem-F4-I-CS1-at0440)
open import Examples.Groups.Clifford+CS.Five.D.D023 using (lem-F4-CS2-CS2-at0440 ; lem-F4-CS2-I-at0440 ; lem-F4-CS2-K2-at0440 ; lem-F4-I-CS2-at0440 ; lem-F4-K2-CS2-at0440)
open import Examples.Groups.Clifford+CS.Five.D.D025 using (lem-F5-12 ; lem-F5-23)
open import Examples.Groups.Clifford+CS.Five.D.D033 using (lem-F4-CS2-K1-at0440)
open import Examples.Groups.Clifford+CS.Five.D.D060 using (lem-F4-CS1-K2-at0440)
open import Examples.Groups.Clifford+CS.Five.D.D061 using (lem-F4-CS1-CS2-at0440 ; lem-F4-CS2-CS1-at0440 ; lem-F4-K2-CS1-at0440)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-comm-push-SBOX⟨2·1·43·0⟩-sw2-R ; lem-comm-push-SBOX⟨3·1·42·0⟩-sw3-R ; lem-comm-push-SBOX⟨4·1·32·0⟩-sw2-R)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-comm-push-SBOX⟨0·1·42·3⟩-sw0-R ; lem-comm-push-SBOX⟨0·2·43·1⟩-sw0-R ; lem-comm-push-SBOX⟨1·0·42·3⟩-sw1-R ; lem-comm-push-SBOX⟨1·2·43·0⟩-sw1-R ; lem-comm-push-SBOX⟨2·0·41·3⟩-sw2-R ; lem-comm-push-SBOX⟨3·0·41·2⟩-sw3-R ; lem-comm-push-SBOX⟨4·0·21·3⟩-sw1-R ; lem-comm-push-SBOX⟨4·1·23·0⟩-sw1-R ; lem-comm-push-SBOX⟨4·2·13·0⟩-sw0-R)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-comm-push-SBOX⟨4·0·12·3⟩-sw0-R ; lem-comm-push-SBOX⟨4·0·31·2⟩-sw2-R)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (K1 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ []) (wl1460 (lit c4))
  q2 : Ws → Eqn
  q2 c4 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wl0018 (lit c4))
  q3 : Ws → Eqn
  q3 c4 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (c₂ (Swap) (CS))
  q4 : Ws → Eqn
  q4 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl0006 (lit c4))
  q5 : Ws → Eqn
  q5 c4 = eqn (CS23 ∷ Sw12 ∷ []) (Sw12 ∷ CS13 ∷ []) (wl0047 (lit c4))
  q6 : Ws → Eqn
  q6 c4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wl0003 (lit c4))
  q7 : Ws → Eqn
  q7 c4 = eqn (Sw34 ∷ Sw34 ∷ []) [] (wl0004 (lit c4))
  q8 : Ws → Eqn
  q8 c4 = eqn (CS12 ∷ Sw34 ∷ []) (Sw34 ∷ CS12 ∷ []) (c₃ (CS ↑) (Swap))
  q9 : Ws → Eqn
  q9 c4 = eqn (CS13 ∷ Sw12 ∷ []) (Sw12 ∷ CS23 ∷ []) (wl0046 (lit c4))
  q10 : Ws → Eqn
  q10 c4 = eqn (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (CS23 ∷ []) (lem-F5-23 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (Sw01 ∷ X4 ∷ []) (X4 ∷ Sw01 ∷ []) (c₂ (Swap) (X ↑ ↑))
  q12 : Ws → Eqn
  q12 c4 = eqn (Sw01 ∷ Sb0-2-43-1 ∷ []) (Sb1-2-43-0 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw0-R (lit c4))
  q13 : Ws → Eqn
  q13 c4 = eqn (Sw12 ∷ X4 ∷ []) (X4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (X ↑))
  q14 : Ws → Eqn
  q14 c4 = eqn (Sw12 ∷ Sb1-2-43-0 ∷ []) (Sb2-1-43-0 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·2·43·0⟩-sw1-R (lit c4))
  q15 : Ws → Eqn
  q15 c4 = eqn (Sw23 ∷ X4 ∷ []) (X4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (X))
  q16 : Ws → Eqn
  q16 c4 = eqn (Sw23 ∷ Sb2-1-43-0 ∷ []) (Sb3-1-42-0 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨2·1·43·0⟩-sw2-R (lit c4))
  q17 : Ws → Eqn
  q17 c4 = eqn (Sw34 ∷ X4 ∷ []) (X3 ∷ Sw34 ∷ []) (wl1456 (lit c4))
  q18 : Ws → Eqn
  q18 c4 = eqn (Sw34 ∷ Sb3-1-42-0 ∷ []) (Sb4-1-32-0 ∷ Sw34 ∷ []) (lem-comm-push-SBOX⟨3·1·42·0⟩-sw3-R (lit c4))
  q19 : Ws → Eqn
  q19 c4 = eqn (Sw23 ∷ X3 ∷ []) (X2 ∷ Sw23 ∷ []) (wl1457 (lit c4))
  q20 : Ws → Eqn
  q20 c4 = eqn (Sw23 ∷ Sb4-1-32-0 ∷ []) (Sb4-1-23-0 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨4·1·32·0⟩-sw2-R (lit c4))
  q21 : Ws → Eqn
  q21 c4 = eqn (Sw12 ∷ X2 ∷ []) (X1 ∷ Sw12 ∷ []) (wl1458 (lit c4))
  q22 : Ws → Eqn
  q22 c4 = eqn (Sw12 ∷ Sb4-1-23-0 ∷ []) (Sb4-2-13-0 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨4·1·23·0⟩-sw1-R (lit c4))
  q23 : Ws → Eqn
  q23 c4 = eqn (Sw01 ∷ X1 ∷ []) (X0 ∷ Sw01 ∷ []) (wl1459 (lit c4))
  q24 : Ws → Eqn
  q24 c4 = eqn (Sw01 ∷ Sb4-2-13-0 ∷ []) (Sb4-2-03-1 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨4·2·13·0⟩-sw0-R (lit c4))
  q25 : Ws → Eqn
  q25 c4 = eqn (X0 ∷ Sb4-2-03-1 ∷ X0 ∷ CK01 ∷ []) (CK01 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ []) (lem-F4-CS2-K1-at0440 c4)
  q26 : Ws → Eqn
  q26 c4 = eqn (K2 ∷ []) (X0 ∷ CK02 ∷ X0 ∷ CK02 ∷ []) (wl1715 (lit c4))
  q27 : Ws → Eqn
  q27 c4 = eqn (X0 ∷ CK02 ∷ X0 ∷ Sb4-2-03-1 ∷ []) (Sb4-2-03-1 ∷ X0 ∷ CK02 ∷ X0 ∷ []) (lem-F4-K2-CS2-at0440 c4)
  q28 : Ws → Eqn
  q28 c4 = eqn (X0 ∷ CK02 ∷ X0 ∷ CK01 ∷ []) (CK01 ∷ X0 ∷ CK02 ∷ X0 ∷ []) (lem-F4-K2-K1-at0440 c4)
  q29 : Ws → Eqn
  q29 c4 = eqn (CS12 ∷ Sw01 ∷ []) (Sw01 ∷ CS02 ∷ []) (wl0146 (lit c4))
  q30 : Ws → Eqn
  q30 c4 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (c₂ (CS) (Swap))
  q31 : Ws → Eqn
  q31 c4 = eqn (CS01 ∷ Sw34 ∷ []) (Sw34 ∷ CS01 ∷ []) (c₂ (CS) (Swap ↑))
  q32 : Ws → Eqn
  q32 c4 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wl0024 (lit c4))
  q33 : Ws → Eqn
  q33 c4 = eqn (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (CS12 ∷ []) (lem-F5-12 c4)
  q34 : Ws → Eqn
  q34 c4 = eqn (Sw01 ∷ Sb0-1-42-3 ∷ []) (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw0-R (lit c4))
  q35 : Ws → Eqn
  q35 c4 = eqn (Sw12 ∷ Sb1-0-42-3 ∷ []) (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·0·42·3⟩-sw1-R (lit c4))
  q36 : Ws → Eqn
  q36 c4 = eqn (Sw23 ∷ Sb2-0-41-3 ∷ []) (Sb3-0-41-2 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨2·0·41·3⟩-sw2-R (lit c4))
  q37 : Ws → Eqn
  q37 c4 = eqn (Sw34 ∷ Sb3-0-41-2 ∷ []) (Sb4-0-31-2 ∷ Sw34 ∷ []) (lem-comm-push-SBOX⟨3·0·41·2⟩-sw3-R (lit c4))
  q38 : Ws → Eqn
  q38 c4 = eqn (Sw23 ∷ Sb4-0-31-2 ∷ []) (Sb4-0-21-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨4·0·31·2⟩-sw2-R (lit c4))
  q39 : Ws → Eqn
  q39 c4 = eqn (Sw12 ∷ Sb4-0-21-3 ∷ []) (Sb4-0-12-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨4·0·21·3⟩-sw1-R (lit c4))
  q40 : Ws → Eqn
  q40 c4 = eqn (Sw01 ∷ Sb4-0-12-3 ∷ []) (Sb4-1-02-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨4·0·12·3⟩-sw0-R (lit c4))
  q41 : Ws → Eqn
  q41 c4 = eqn (X0 ∷ Sb4-1-02-3 ∷ X0 ∷ CK02 ∷ []) (CK02 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ []) (lem-F4-CS1-K2-at0440 c4)
  q42 : Ws → Eqn
  q42 c4 = eqn (X0 ∷ Sb4-1-02-3 ∷ X0 ∷ Sb4-2-03-1 ∷ []) (Sb4-2-03-1 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ []) (lem-F4-CS1-CS2-at0440 c4)
  q43 : Ws → Eqn
  q43 c4 = eqn (X0 ∷ Sb4-1-02-3 ∷ X0 ∷ CK01 ∷ []) (CK01 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ []) (lem-F4-CS1-K1-at0440 c4)
  q44 : Ws → Eqn
  q44 c4 = eqn (X0 ∷ Sb4-1-02-3 ∷ X0 ∷ Sb4-1-02-3 ∷ []) (Sb4-1-02-3 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ []) (lem-F4-CS1-CS1-at0440 c4)
  q45 : Ws → Eqn
  q45 c4 = eqn (X0 ∷ CK02 ∷ X0 ∷ Sb4-1-02-3 ∷ []) (Sb4-1-02-3 ∷ X0 ∷ CK02 ∷ X0 ∷ []) (lem-F4-K2-CS1-at0440 c4)
  q46 : Ws → Eqn
  q46 c4 = eqn (X0 ∷ CK02 ∷ X0 ∷ CK02 ∷ []) (CK02 ∷ X0 ∷ CK02 ∷ X0 ∷ []) (lem-F4-K2-K2-at0440 c4)
  q47 : Ws → Eqn
  q47 c4 = eqn (X0 ∷ S0 ∷ X0 ∷ S0 ∷ []) (ι ∷ []) (wl1461 (lit c4))
  q48 : Ws → Eqn
  q48 c4 = eqn (X0 ∷ S0 ∷ X0 ∷ CK02 ∷ []) (CK02 ∷ X0 ∷ S0 ∷ X0 ∷ []) (lem-F4-I-K2-at0440 c4)
  q49 : Ws → Eqn
  q49 c4 = eqn (X0 ∷ S0 ∷ X0 ∷ Sb4-1-02-3 ∷ []) (Sb4-1-02-3 ∷ X0 ∷ S0 ∷ X0 ∷ []) (lem-F4-I-CS1-at0440 c4)
  q50 : Ws → Eqn
  q50 c4 = eqn (X0 ∷ S0 ∷ X0 ∷ Sb4-2-03-1 ∷ []) (Sb4-2-03-1 ∷ X0 ∷ S0 ∷ X0 ∷ []) (lem-F4-I-CS2-at0440 c4)
  q51 : Ws → Eqn
  q51 c4 = eqn (X0 ∷ S0 ∷ X0 ∷ CK01 ∷ []) (CK01 ∷ X0 ∷ S0 ∷ X0 ∷ []) (lem-F4-I-K1-at0440 c4)
  q52 : Ws → Eqn
  q52 c4 = eqn (X0 ∷ Sb4-2-03-1 ∷ X0 ∷ S0 ∷ []) (S0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ []) (lem-F4-CS2-I-at0440 c4)
  q53 : Ws → Eqn
  q53 c4 = eqn (X0 ∷ Sb4-2-03-1 ∷ X0 ∷ CK02 ∷ []) (CK02 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ []) (lem-F4-CS2-K2-at0440 c4)
  q54 : Ws → Eqn
  q54 c4 = eqn (X0 ∷ Sb4-2-03-1 ∷ X0 ∷ Sb4-1-02-3 ∷ []) (Sb4-1-02-3 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ []) (lem-F4-CS2-CS1-at0440 c4)
  q55 : Ws → Eqn
  q55 c4 = eqn (X0 ∷ Sb4-2-03-1 ∷ X0 ∷ Sb4-2-03-1 ∷ []) (Sb4-2-03-1 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ []) (lem-F4-CS2-CS2-at0440 c4)

-- ckt-TST @0440 part0: 253 steps
lem-ckt-TST-at0440-part0 : Ws → ⟪ (K1 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ Sb2-4-01-3 ∷ K1 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw23 ∷ CS13 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ Sb2-4-01-3 ∷ K1 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ []) ⟫ʷ
lem-ckt-TST-at0440-part0 c4 = derive (K1 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ Sb2-4-01-3 ∷ K1 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ []) (X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw23 ∷ CS13 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ Sb2-4-01-3 ∷ K1 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ [])
  (rw 0 (q1 c4) ∷
   rw⁻ 5 (q2 c4) ∷
   rw⁻ 4 (q3 c4) ∷
   rw⁻ 6 (q4 c4) ∷
   rw 5 (q5 c4) ∷
   rw⁻ 7 (q6 c4) ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 (q6 c4) ∷
   rw⁻ 8 (q7 c4) ∷
   rw 7 (q8 c4) ∷
   rw⁻ 9 (q6 c4) ∷
   rw⁻ 8 (q6 c4) ∷
   re 9 3 (CS13 ∷ []) ∷
   rw⁻ 10 (q4 c4) ∷
   rw 9 (q9 c4) ∷
   rw⁻ 11 (q2 c4) ∷
   rw⁻ 10 (q3 c4) ∷
   rw⁻ 11 (q10 c4) ∷
   rw 10 (q11 c4) ∷
   rw 11 (q12 c4) ∷
   rw 12 (q11 c4) ∷
   rw 13 (q12 c4) ∷
   rw 14 (q2 c4) ∷
   rw 9 (q13 c4) ∷
   rw 10 (q14 c4) ∷
   rw 11 (q13 c4) ∷
   rw 12 (q14 c4) ∷
   rw 13 (q4 c4) ∷
   rw 8 (q15 c4) ∷
   rw 9 (q16 c4) ∷
   rw 10 (q15 c4) ∷
   rw 11 (q16 c4) ∷
   rw 12 (q6 c4) ∷
   rw 7 (q17 c4) ∷
   rw 8 (q18 c4) ∷
   rw 9 (q17 c4) ∷
   rw 10 (q18 c4) ∷
   rw 11 (q7 c4) ∷
   rw 6 (q19 c4) ∷
   rw 7 (q20 c4) ∷
   rw 8 (q19 c4) ∷
   rw 9 (q20 c4) ∷
   rw 10 (q6 c4) ∷
   rw 5 (q21 c4) ∷
   rw 6 (q22 c4) ∷
   rw 7 (q21 c4) ∷
   rw 8 (q22 c4) ∷
   rw 9 (q4 c4) ∷
   rw 4 (q23 c4) ∷
   rw 5 (q24 c4) ∷
   rw 6 (q23 c4) ∷
   rw 7 (q24 c4) ∷
   rw 8 (q2 c4) ∷
   rw⁻ 3 (q25 c4) ∷
   rw 8 (q26 c4) ∷
   rw⁻ 7 (q27 c4) ∷
   rw⁻ 6 (q28 c4) ∷
   rw⁻ 13 (q2 c4) ∷
   rw 12 (q29 c4) ∷
   rw⁻ 14 (q4 c4) ∷
   re 13 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 15 (q4 c4) ∷
   rw⁻ 15 (q6 c4) ∷
   rw 14 (q30 c4) ∷
   rw⁻ 16 (q7 c4) ∷
   rw 15 (q31 c4) ∷
   rw⁻ 17 (q6 c4) ∷
   rw 16 (q30 c4) ∷
   rw⁻ 18 (q4 c4) ∷
   rw⁻ 17 (q4 c4) ∷
   re 18 3 (CS02 ∷ []) ∷
   rw⁻ 19 (q2 c4) ∷
   rw 18 (q32 c4) ∷
   rw⁻ 19 (q33 c4) ∷
   rw 18 (q11 c4) ∷
   rw 19 (q34 c4) ∷
   rw 20 (q11 c4) ∷
   rw 21 (q34 c4) ∷
   rw 22 (q2 c4) ∷
   rw 17 (q13 c4) ∷
   rw 18 (q35 c4) ∷
   rw 19 (q13 c4) ∷
   rw 20 (q35 c4) ∷
   rw 21 (q4 c4) ∷
   rw 16 (q15 c4) ∷
   rw 17 (q36 c4) ∷
   rw 18 (q15 c4) ∷
   rw 19 (q36 c4) ∷
   rw 20 (q6 c4) ∷
   rw 15 (q17 c4) ∷
   rw 16 (q37 c4) ∷
   rw 17 (q17 c4) ∷
   rw 18 (q37 c4) ∷
   rw 19 (q7 c4) ∷
   rw 14 (q19 c4) ∷
   rw 15 (q38 c4) ∷
   rw 16 (q19 c4) ∷
   rw 17 (q38 c4) ∷
   rw 18 (q6 c4) ∷
   rw 13 (q21 c4) ∷
   rw 14 (q39 c4) ∷
   rw 15 (q21 c4) ∷
   rw 16 (q39 c4) ∷
   rw 17 (q4 c4) ∷
   rw 12 (q23 c4) ∷
   rw 13 (q40 c4) ∷
   rw 14 (q23 c4) ∷
   rw 15 (q40 c4) ∷
   rw 16 (q2 c4) ∷
   rw⁻ 11 (q41 c4) ∷
   rw⁻ 10 (q42 c4) ∷
   rw⁻ 9 (q43 c4) ∷
   rw⁻ 17 (q2 c4) ∷
   rw 16 (q29 c4) ∷
   rw⁻ 18 (q4 c4) ∷
   re 17 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 19 (q4 c4) ∷
   rw⁻ 19 (q6 c4) ∷
   rw 18 (q30 c4) ∷
   rw⁻ 20 (q7 c4) ∷
   rw 19 (q31 c4) ∷
   rw⁻ 21 (q6 c4) ∷
   rw 20 (q30 c4) ∷
   rw⁻ 22 (q4 c4) ∷
   rw⁻ 21 (q4 c4) ∷
   re 22 3 (CS02 ∷ []) ∷
   rw⁻ 23 (q2 c4) ∷
   rw 22 (q32 c4) ∷
   rw⁻ 23 (q33 c4) ∷
   rw 22 (q11 c4) ∷
   rw 23 (q34 c4) ∷
   rw 24 (q11 c4) ∷
   rw 25 (q34 c4) ∷
   rw 26 (q2 c4) ∷
   rw 21 (q13 c4) ∷
   rw 22 (q35 c4) ∷
   rw 23 (q13 c4) ∷
   rw 24 (q35 c4) ∷
   rw 25 (q4 c4) ∷
   rw 20 (q15 c4) ∷
   rw 21 (q36 c4) ∷
   rw 22 (q15 c4) ∷
   rw 23 (q36 c4) ∷
   rw 24 (q6 c4) ∷
   rw 19 (q17 c4) ∷
   rw 20 (q37 c4) ∷
   rw 21 (q17 c4) ∷
   rw 22 (q37 c4) ∷
   rw 23 (q7 c4) ∷
   rw 18 (q19 c4) ∷
   rw 19 (q38 c4) ∷
   rw 20 (q19 c4) ∷
   rw 21 (q38 c4) ∷
   rw 22 (q6 c4) ∷
   rw 17 (q21 c4) ∷
   rw 18 (q39 c4) ∷
   rw 19 (q21 c4) ∷
   rw 20 (q39 c4) ∷
   rw 21 (q4 c4) ∷
   rw 16 (q23 c4) ∷
   rw 17 (q40 c4) ∷
   rw 18 (q23 c4) ∷
   rw 19 (q40 c4) ∷
   rw 20 (q2 c4) ∷
   rw⁻ 15 (q44 c4) ∷
   rw⁻ 14 (q41 c4) ∷
   rw⁻ 13 (q42 c4) ∷
   rw⁻ 12 (q43 c4) ∷
   rw 20 (q26 c4) ∷
   rw⁻ 19 (q45 c4) ∷
   rw⁻ 18 (q45 c4) ∷
   rw⁻ 17 (q46 c4) ∷
   rw⁻ 16 (q27 c4) ∷
   rw⁻ 15 (q28 c4) ∷
   rw⁻ 24 (q47 c4) ∷
   rw⁻ 23 (q48 c4) ∷
   rw⁻ 22 (q49 c4) ∷
   rw⁻ 21 (q49 c4) ∷
   rw⁻ 20 (q48 c4) ∷
   rw⁻ 19 (q50 c4) ∷
   rw⁻ 18 (q51 c4) ∷
   rw⁻ 29 (q2 c4) ∷
   rw⁻ 28 (q3 c4) ∷
   rw⁻ 30 (q4 c4) ∷
   rw 29 (q5 c4) ∷
   rw⁻ 31 (q6 c4) ∷
   re 30 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 32 (q6 c4) ∷
   rw⁻ 32 (q7 c4) ∷
   rw 31 (q8 c4) ∷
   rw⁻ 33 (q6 c4) ∷
   rw⁻ 32 (q6 c4) ∷
   re 33 3 (CS13 ∷ []) ∷
   rw⁻ 34 (q4 c4) ∷
   rw 33 (q9 c4) ∷
   rw⁻ 35 (q2 c4) ∷
   rw⁻ 34 (q3 c4) ∷
   rw⁻ 35 (q10 c4) ∷
   rw 34 (q11 c4) ∷
   rw 35 (q12 c4) ∷
   rw 36 (q11 c4) ∷
   rw 37 (q12 c4) ∷
   rw 38 (q2 c4) ∷
   rw 33 (q13 c4) ∷
   rw 34 (q14 c4) ∷
   rw 35 (q13 c4) ∷
   rw 36 (q14 c4) ∷
   rw 37 (q4 c4) ∷
   rw 32 (q15 c4) ∷
   rw 33 (q16 c4) ∷
   rw 34 (q15 c4) ∷
   rw 35 (q16 c4) ∷
   rw 36 (q6 c4) ∷
   rw 31 (q17 c4) ∷
   rw 32 (q18 c4) ∷
   rw 33 (q17 c4) ∷
   rw 34 (q18 c4) ∷
   rw 35 (q7 c4) ∷
   rw 30 (q19 c4) ∷
   rw 31 (q20 c4) ∷
   rw 32 (q19 c4) ∷
   rw 33 (q20 c4) ∷
   rw 34 (q6 c4) ∷
   rw 29 (q21 c4) ∷
   rw 30 (q22 c4) ∷
   rw 31 (q21 c4) ∷
   rw 32 (q22 c4) ∷
   rw 33 (q4 c4) ∷
   rw 28 (q23 c4) ∷
   rw 29 (q24 c4) ∷
   rw 30 (q23 c4) ∷
   rw 31 (q24 c4) ∷
   rw 32 (q2 c4) ∷
   rw⁻ 27 (q52 c4) ∷
   rw⁻ 26 (q53 c4) ∷
   rw⁻ 25 (q54 c4) ∷
   rw⁻ 24 (q54 c4) ∷
   rw⁻ 23 (q53 c4) ∷
   rw⁻ 22 (q55 c4) ∷
   rw⁻ 21 (q25 c4) ∷
   rw⁻ 33 (q2 c4) ∷
   rw⁻ 32 (q3 c4) ∷
   rw⁻ 34 (q4 c4) ∷
   rw 33 (q5 c4) ∷
   rw⁻ 35 (q6 c4) ∷
   re 34 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 36 (q6 c4) ∷
   rw⁻ 36 (q7 c4) ∷
   rw 35 (q8 c4) ∷
   rw⁻ 37 (q6 c4) ∷
   rw⁻ 36 (q6 c4) ∷
   re 37 3 (CS13 ∷ []) ∷
   rw⁻ 38 (q4 c4) ∷ []) Eq.refl

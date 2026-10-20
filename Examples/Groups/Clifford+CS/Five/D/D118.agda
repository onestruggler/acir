{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D118 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0003 ; wl0004 ; wl0006 ; wl0018 ; wl0046 ; wl0047 ; wl1456 ; wl1457 ; wl1458 ; wl1459 ; wl1715)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-F4-K2-I-at0440 ; lem-F4-K2-K2-at0440)
open import Examples.Groups.Clifford+CS.Five.D.D023 using (lem-F4-CS2-CS2-at0440 ; lem-F4-CS2-I-at0440 ; lem-F4-CS2-K2-at0440 ; lem-F4-K2-CS2-at0440)
open import Examples.Groups.Clifford+CS.Five.D.D025 using (lem-F5-23)
open import Examples.Groups.Clifford+CS.Five.D.D033 using (lem-F4-CS2-K1-at0440)
open import Examples.Groups.Clifford+CS.Five.D.D061 using (lem-F4-CS2-CS1-at0440 ; lem-F4-K2-CS1-at0440)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-comm-push-SBOX⟨2·1·43·0⟩-sw2-R ; lem-comm-push-SBOX⟨3·1·42·0⟩-sw3-R ; lem-comm-push-SBOX⟨4·1·32·0⟩-sw2-R)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-comm-push-SBOX⟨0·2·43·1⟩-sw0-R ; lem-comm-push-SBOX⟨1·2·43·0⟩-sw1-R ; lem-comm-push-SBOX⟨4·1·23·0⟩-sw1-R ; lem-comm-push-SBOX⟨4·2·13·0⟩-sw0-R)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (Sw01 ∷ Sb0-2-43-1 ∷ []) (Sb1-2-43-0 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw0-R (lit c4))
  q2 : Ws → Eqn
  q2 c4 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wl0018 (lit c4))
  q3 : Ws → Eqn
  q3 c4 = eqn (Sw12 ∷ X4 ∷ []) (X4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (X ↑))
  q4 : Ws → Eqn
  q4 c4 = eqn (Sw12 ∷ Sb1-2-43-0 ∷ []) (Sb2-1-43-0 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·2·43·0⟩-sw1-R (lit c4))
  q5 : Ws → Eqn
  q5 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl0006 (lit c4))
  q6 : Ws → Eqn
  q6 c4 = eqn (Sw23 ∷ X4 ∷ []) (X4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (X))
  q7 : Ws → Eqn
  q7 c4 = eqn (Sw23 ∷ Sb2-1-43-0 ∷ []) (Sb3-1-42-0 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨2·1·43·0⟩-sw2-R (lit c4))
  q8 : Ws → Eqn
  q8 c4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wl0003 (lit c4))
  q9 : Ws → Eqn
  q9 c4 = eqn (Sw34 ∷ X4 ∷ []) (X3 ∷ Sw34 ∷ []) (wl1456 (lit c4))
  q10 : Ws → Eqn
  q10 c4 = eqn (Sw34 ∷ Sb3-1-42-0 ∷ []) (Sb4-1-32-0 ∷ Sw34 ∷ []) (lem-comm-push-SBOX⟨3·1·42·0⟩-sw3-R (lit c4))
  q11 : Ws → Eqn
  q11 c4 = eqn (Sw34 ∷ Sw34 ∷ []) [] (wl0004 (lit c4))
  q12 : Ws → Eqn
  q12 c4 = eqn (Sw23 ∷ X3 ∷ []) (X2 ∷ Sw23 ∷ []) (wl1457 (lit c4))
  q13 : Ws → Eqn
  q13 c4 = eqn (Sw23 ∷ Sb4-1-32-0 ∷ []) (Sb4-1-23-0 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨4·1·32·0⟩-sw2-R (lit c4))
  q14 : Ws → Eqn
  q14 c4 = eqn (Sw12 ∷ X2 ∷ []) (X1 ∷ Sw12 ∷ []) (wl1458 (lit c4))
  q15 : Ws → Eqn
  q15 c4 = eqn (Sw12 ∷ Sb4-1-23-0 ∷ []) (Sb4-2-13-0 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨4·1·23·0⟩-sw1-R (lit c4))
  q16 : Ws → Eqn
  q16 c4 = eqn (Sw01 ∷ X1 ∷ []) (X0 ∷ Sw01 ∷ []) (wl1459 (lit c4))
  q17 : Ws → Eqn
  q17 c4 = eqn (Sw01 ∷ Sb4-2-13-0 ∷ []) (Sb4-2-03-1 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨4·2·13·0⟩-sw0-R (lit c4))
  q18 : Ws → Eqn
  q18 c4 = eqn (X0 ∷ Sb4-2-03-1 ∷ X0 ∷ Sb4-2-03-1 ∷ []) (Sb4-2-03-1 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ []) (lem-F4-CS2-CS2-at0440 c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (X0 ∷ Sb4-2-03-1 ∷ X0 ∷ S0 ∷ []) (S0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ []) (lem-F4-CS2-I-at0440 c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (X0 ∷ Sb4-2-03-1 ∷ X0 ∷ CK02 ∷ []) (CK02 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ []) (lem-F4-CS2-K2-at0440 c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (X0 ∷ Sb4-2-03-1 ∷ X0 ∷ Sb4-1-02-3 ∷ []) (Sb4-1-02-3 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ []) (lem-F4-CS2-CS1-at0440 c4)
  q22 : Ws → Eqn
  q22 c4 = eqn (X0 ∷ Sb4-2-03-1 ∷ X0 ∷ CK01 ∷ []) (CK01 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ []) (lem-F4-CS2-K1-at0440 c4)
  q23 : Ws → Eqn
  q23 c4 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (c₂ (Swap) (CS))
  q24 : Ws → Eqn
  q24 c4 = eqn (CS23 ∷ Sw12 ∷ []) (Sw12 ∷ CS13 ∷ []) (wl0047 (lit c4))
  q25 : Ws → Eqn
  q25 c4 = eqn (CS12 ∷ Sw34 ∷ []) (Sw34 ∷ CS12 ∷ []) (c₃ (CS ↑) (Swap))
  q26 : Ws → Eqn
  q26 c4 = eqn (CS13 ∷ Sw12 ∷ []) (Sw12 ∷ CS23 ∷ []) (wl0046 (lit c4))
  q27 : Ws → Eqn
  q27 c4 = eqn (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (CS23 ∷ []) (lem-F5-23 c4)
  q28 : Ws → Eqn
  q28 c4 = eqn (Sw01 ∷ X4 ∷ []) (X4 ∷ Sw01 ∷ []) (c₂ (Swap) (X ↑ ↑))
  q29 : Ws → Eqn
  q29 c4 = eqn (K2 ∷ []) (X0 ∷ CK02 ∷ X0 ∷ CK02 ∷ []) (wl1715 (lit c4))
  q30 : Ws → Eqn
  q30 c4 = eqn (X0 ∷ CK02 ∷ X0 ∷ Sb4-2-03-1 ∷ []) (Sb4-2-03-1 ∷ X0 ∷ CK02 ∷ X0 ∷ []) (lem-F4-K2-CS2-at0440 c4)
  q31 : Ws → Eqn
  q31 c4 = eqn (X0 ∷ CK02 ∷ X0 ∷ S0 ∷ []) (S0 ∷ X0 ∷ CK02 ∷ X0 ∷ []) (lem-F4-K2-I-at0440 c4)
  q32 : Ws → Eqn
  q32 c4 = eqn (X0 ∷ CK02 ∷ X0 ∷ CK02 ∷ []) (CK02 ∷ X0 ∷ CK02 ∷ X0 ∷ []) (lem-F4-K2-K2-at0440 c4)
  q33 : Ws → Eqn
  q33 c4 = eqn (X0 ∷ CK02 ∷ X0 ∷ Sb4-1-02-3 ∷ []) (Sb4-1-02-3 ∷ X0 ∷ CK02 ∷ X0 ∷ []) (lem-F4-K2-CS1-at0440 c4)

-- ckt-TST @0440 part16: 108 steps
lem-ckt-TST-at0440-part16 : Ws → ⟪ (X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK01 ∷ S0 ∷ Sb2-4-01-3 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ X4 ∷ Sb1-2-43-0 ∷ X4 ∷ Sw01 ∷ Sb0-2-43-1 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK01 ∷ S0 ∷ Sb2-4-01-3 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ X0 ∷ CK02 ∷ X0 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ []) ⟫ʷ
lem-ckt-TST-at0440-part16 c4 = derive (X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK01 ∷ S0 ∷ Sb2-4-01-3 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ X4 ∷ Sb1-2-43-0 ∷ X4 ∷ Sw01 ∷ Sb0-2-43-1 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ []) (X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK01 ∷ S0 ∷ Sb2-4-01-3 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ X0 ∷ CK02 ∷ X0 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ [])
  (rw 234 (q1 c4) ∷
   rw 235 (q2 c4) ∷
   rw 230 (q3 c4) ∷
   rw 231 (q4 c4) ∷
   rw 232 (q3 c4) ∷
   rw 233 (q4 c4) ∷
   rw 234 (q5 c4) ∷
   rw 229 (q6 c4) ∷
   rw 230 (q7 c4) ∷
   rw 231 (q6 c4) ∷
   rw 232 (q7 c4) ∷
   rw 233 (q8 c4) ∷
   rw 228 (q9 c4) ∷
   rw 229 (q10 c4) ∷
   rw 230 (q9 c4) ∷
   rw 231 (q10 c4) ∷
   rw 232 (q11 c4) ∷
   rw 227 (q12 c4) ∷
   rw 228 (q13 c4) ∷
   rw 229 (q12 c4) ∷
   rw 230 (q13 c4) ∷
   rw 231 (q8 c4) ∷
   rw 226 (q14 c4) ∷
   rw 227 (q15 c4) ∷
   rw 228 (q14 c4) ∷
   rw 229 (q15 c4) ∷
   rw 230 (q5 c4) ∷
   rw 225 (q16 c4) ∷
   rw 226 (q17 c4) ∷
   rw 227 (q16 c4) ∷
   rw 228 (q17 c4) ∷
   rw 229 (q2 c4) ∷
   rw⁻ 224 (q18 c4) ∷
   rw⁻ 223 (q19 c4) ∷
   rw⁻ 222 (q20 c4) ∷
   rw⁻ 221 (q21 c4) ∷
   rw⁻ 220 (q21 c4) ∷
   rw⁻ 219 (q20 c4) ∷
   rw⁻ 218 (q18 c4) ∷
   rw⁻ 217 (q22 c4) ∷
   rw⁻ 230 (q2 c4) ∷
   rw⁻ 229 (q23 c4) ∷
   rw⁻ 231 (q5 c4) ∷
   rw 230 (q24 c4) ∷
   rw⁻ 232 (q8 c4) ∷
   re 231 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 233 (q8 c4) ∷
   rw⁻ 233 (q11 c4) ∷
   rw 232 (q25 c4) ∷
   rw⁻ 234 (q8 c4) ∷
   rw⁻ 233 (q8 c4) ∷
   re 234 3 (CS13 ∷ []) ∷
   rw⁻ 235 (q5 c4) ∷
   rw 234 (q26 c4) ∷
   rw⁻ 236 (q2 c4) ∷
   rw⁻ 235 (q23 c4) ∷
   rw⁻ 236 (q27 c4) ∷
   rw 235 (q28 c4) ∷
   rw 236 (q1 c4) ∷
   rw 237 (q28 c4) ∷
   rw 238 (q1 c4) ∷
   rw 239 (q2 c4) ∷
   rw 234 (q3 c4) ∷
   rw 235 (q4 c4) ∷
   rw 236 (q3 c4) ∷
   rw 237 (q4 c4) ∷
   rw 238 (q5 c4) ∷
   rw 233 (q6 c4) ∷
   rw 234 (q7 c4) ∷
   rw 235 (q6 c4) ∷
   rw 236 (q7 c4) ∷
   rw 237 (q8 c4) ∷
   rw 232 (q9 c4) ∷
   rw 233 (q10 c4) ∷
   rw 234 (q9 c4) ∷
   rw 235 (q10 c4) ∷
   rw 236 (q11 c4) ∷
   rw 231 (q12 c4) ∷
   rw 232 (q13 c4) ∷
   rw 233 (q12 c4) ∷
   rw 234 (q13 c4) ∷
   rw 235 (q8 c4) ∷
   rw 230 (q14 c4) ∷
   rw 231 (q15 c4) ∷
   rw 232 (q14 c4) ∷
   rw 233 (q15 c4) ∷
   rw 234 (q5 c4) ∷
   rw 229 (q16 c4) ∷
   rw 230 (q17 c4) ∷
   rw 231 (q16 c4) ∷
   rw 232 (q17 c4) ∷
   rw 233 (q2 c4) ∷
   rw⁻ 228 (q18 c4) ∷
   rw⁻ 227 (q18 c4) ∷
   rw⁻ 226 (q19 c4) ∷
   rw⁻ 225 (q20 c4) ∷
   rw⁻ 224 (q21 c4) ∷
   rw⁻ 223 (q21 c4) ∷
   rw⁻ 222 (q20 c4) ∷
   rw⁻ 221 (q18 c4) ∷
   rw⁻ 220 (q22 c4) ∷
   rw 233 (q29 c4) ∷
   rw⁻ 232 (q30 c4) ∷
   rw⁻ 231 (q30 c4) ∷
   rw⁻ 230 (q30 c4) ∷
   rw⁻ 229 (q31 c4) ∷
   rw⁻ 228 (q32 c4) ∷
   rw⁻ 227 (q33 c4) ∷ []) Eq.refl

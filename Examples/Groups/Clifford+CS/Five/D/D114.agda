{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D114 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D023 using (lem-F4-CS2-CS2-at0440 ; lem-F4-CS2-I-at0440 ; lem-F4-CS2-K2-at0440)
open import Examples.Groups.Clifford+CS.Five.D.D025 using (lem-F5-23)
open import Examples.Groups.Clifford+CS.Five.D.D033 using (lem-F4-CS2-K1-at0440)
open import Examples.Groups.Clifford+CS.Five.D.D061 using (lem-F4-CS2-CS1-at0440 ; lem-F4-CS2-K3-at0440)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-comm-push-SBOX⟨2·1·43·0⟩-sw2-R ; lem-comm-push-SBOX⟨3·1·42·0⟩-sw3-R ; lem-comm-push-SBOX⟨4·1·32·0⟩-sw2-R)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-comm-push-SBOX⟨0·2·43·1⟩-sw0-R ; lem-comm-push-SBOX⟨1·2·43·0⟩-sw1-R ; lem-comm-push-SBOX⟨4·1·23·0⟩-sw1-R ; lem-comm-push-SBOX⟨4·2·13·0⟩-sw0-R)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (Sw23 ∷ Sb2-1-43-0 ∷ []) (Sb3-1-42-0 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨2·1·43·0⟩-sw2-R (lit c4))
  q2 : Ws → Eqn
  q2 c4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wl 3 (lit c4))
  q3 : Ws → Eqn
  q3 c4 = eqn (Sw34 ∷ X4 ∷ []) (X3 ∷ Sw34 ∷ []) (wl 1456 (lit c4))
  q4 : Ws → Eqn
  q4 c4 = eqn (Sw34 ∷ Sb3-1-42-0 ∷ []) (Sb4-1-32-0 ∷ Sw34 ∷ []) (lem-comm-push-SBOX⟨3·1·42·0⟩-sw3-R (lit c4))
  q5 : Ws → Eqn
  q5 c4 = eqn (Sw34 ∷ Sw34 ∷ []) [] (wl 4 (lit c4))
  q6 : Ws → Eqn
  q6 c4 = eqn (Sw23 ∷ X3 ∷ []) (X2 ∷ Sw23 ∷ []) (wl 1457 (lit c4))
  q7 : Ws → Eqn
  q7 c4 = eqn (Sw23 ∷ Sb4-1-32-0 ∷ []) (Sb4-1-23-0 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨4·1·32·0⟩-sw2-R (lit c4))
  q8 : Ws → Eqn
  q8 c4 = eqn (Sw12 ∷ X2 ∷ []) (X1 ∷ Sw12 ∷ []) (wl 1458 (lit c4))
  q9 : Ws → Eqn
  q9 c4 = eqn (Sw12 ∷ Sb4-1-23-0 ∷ []) (Sb4-2-13-0 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨4·1·23·0⟩-sw1-R (lit c4))
  q10 : Ws → Eqn
  q10 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl 6 (lit c4))
  q11 : Ws → Eqn
  q11 c4 = eqn (Sw01 ∷ X1 ∷ []) (X0 ∷ Sw01 ∷ []) (wl 1459 (lit c4))
  q12 : Ws → Eqn
  q12 c4 = eqn (Sw01 ∷ Sb4-2-13-0 ∷ []) (Sb4-2-03-1 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨4·2·13·0⟩-sw0-R (lit c4))
  q13 : Ws → Eqn
  q13 c4 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wl 18 (lit c4))
  q14 : Ws → Eqn
  q14 c4 = eqn (X0 ∷ Sb4-2-03-1 ∷ X0 ∷ CK03 ∷ []) (CK03 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ []) (lem-F4-CS2-K3-at0440 c4)
  q15 : Ws → Eqn
  q15 c4 = eqn (X0 ∷ Sb4-2-03-1 ∷ X0 ∷ S0 ∷ []) (S0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ []) (lem-F4-CS2-I-at0440 c4)
  q16 : Ws → Eqn
  q16 c4 = eqn (X0 ∷ Sb4-2-03-1 ∷ X0 ∷ CK02 ∷ []) (CK02 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ []) (lem-F4-CS2-K2-at0440 c4)
  q17 : Ws → Eqn
  q17 c4 = eqn (X0 ∷ Sb4-2-03-1 ∷ X0 ∷ Sb4-2-03-1 ∷ []) (Sb4-2-03-1 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ []) (lem-F4-CS2-CS2-at0440 c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (X0 ∷ Sb4-2-03-1 ∷ X0 ∷ Sb4-1-02-3 ∷ []) (Sb4-1-02-3 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ []) (lem-F4-CS2-CS1-at0440 c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (X0 ∷ Sb4-2-03-1 ∷ X0 ∷ CK01 ∷ []) (CK01 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ []) (lem-F4-CS2-K1-at0440 c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (c₂ (Swap) (CS))
  q21 : Ws → Eqn
  q21 c4 = eqn (CS23 ∷ Sw12 ∷ []) (Sw12 ∷ CS13 ∷ []) (wl 47 (lit c4))
  q22 : Ws → Eqn
  q22 c4 = eqn (CS12 ∷ Sw34 ∷ []) (Sw34 ∷ CS12 ∷ []) (c₃ (CS ↑) (Swap))
  q23 : Ws → Eqn
  q23 c4 = eqn (CS13 ∷ Sw12 ∷ []) (Sw12 ∷ CS23 ∷ []) (wl 46 (lit c4))
  q24 : Ws → Eqn
  q24 c4 = eqn (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (CS23 ∷ []) (lem-F5-23 c4)
  q25 : Ws → Eqn
  q25 c4 = eqn (Sw01 ∷ X4 ∷ []) (X4 ∷ Sw01 ∷ []) (c₂ (Swap) (X ↑ ↑))
  q26 : Ws → Eqn
  q26 c4 = eqn (Sw01 ∷ Sb0-2-43-1 ∷ []) (Sb1-2-43-0 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw0-R (lit c4))
  q27 : Ws → Eqn
  q27 c4 = eqn (Sw12 ∷ X4 ∷ []) (X4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (X ↑))
  q28 : Ws → Eqn
  q28 c4 = eqn (Sw12 ∷ Sb1-2-43-0 ∷ []) (Sb2-1-43-0 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·2·43·0⟩-sw1-R (lit c4))
  q29 : Ws → Eqn
  q29 c4 = eqn (Sw23 ∷ X4 ∷ []) (X4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (X))

-- ckt-TST @0440 part11: 129 steps
lem-ckt-TST-at0440-part11 : Ws → ⟪ (X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ X4 ∷ Sb3-1-42-0 ∷ X4 ∷ Sw23 ∷ Sb2-1-43-0 ∷ Sw23 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ Sb2-4-01-3 ∷ K1 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ Sb2-4-01-3 ∷ K1 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ []) ⟫ʷ
lem-ckt-TST-at0440-part11 c4 = derive (X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ X4 ∷ Sb3-1-42-0 ∷ X4 ∷ Sw23 ∷ Sb2-1-43-0 ∷ Sw23 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ Sb2-4-01-3 ∷ K1 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ []) (X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ Sb2-4-01-3 ∷ K1 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ [])
  (rw 175 (q1 c4) ∷
   rw 176 (q2 c4) ∷
   rw 171 (q3 c4) ∷
   rw 172 (q4 c4) ∷
   rw 173 (q3 c4) ∷
   rw 174 (q4 c4) ∷
   rw 175 (q5 c4) ∷
   rw 170 (q6 c4) ∷
   rw 171 (q7 c4) ∷
   rw 172 (q6 c4) ∷
   rw 173 (q7 c4) ∷
   rw 174 (q2 c4) ∷
   rw 169 (q8 c4) ∷
   rw 170 (q9 c4) ∷
   rw 171 (q8 c4) ∷
   rw 172 (q9 c4) ∷
   rw 173 (q10 c4) ∷
   rw 168 (q11 c4) ∷
   rw 169 (q12 c4) ∷
   rw 170 (q11 c4) ∷
   rw 171 (q12 c4) ∷
   rw 172 (q13 c4) ∷
   rw⁻ 167 (q14 c4) ∷
   rw⁻ 166 (q15 c4) ∷
   rw⁻ 165 (q16 c4) ∷
   rw⁻ 164 (q17 c4) ∷
   rw⁻ 163 (q17 c4) ∷
   rw⁻ 162 (q16 c4) ∷
   rw⁻ 161 (q15 c4) ∷
   rw⁻ 160 (q14 c4) ∷
   rw⁻ 159 (q17 c4) ∷
   rw⁻ 158 (q17 c4) ∷
   rw⁻ 157 (q14 c4) ∷
   rw⁻ 156 (q18 c4) ∷
   rw⁻ 155 (q15 c4) ∷
   rw⁻ 154 (q14 c4) ∷
   rw⁻ 153 (q17 c4) ∷
   rw⁻ 152 (q17 c4) ∷
   rw⁻ 151 (q14 c4) ∷
   rw⁻ 150 (q15 c4) ∷
   rw⁻ 149 (q16 c4) ∷
   rw⁻ 148 (q17 c4) ∷
   rw⁻ 147 (q17 c4) ∷
   rw⁻ 146 (q16 c4) ∷
   rw⁻ 145 (q15 c4) ∷
   rw⁻ 144 (q14 c4) ∷
   rw⁻ 143 (q17 c4) ∷
   rw⁻ 142 (q17 c4) ∷
   rw⁻ 141 (q14 c4) ∷
   rw⁻ 140 (q15 c4) ∷
   rw⁻ 139 (q16 c4) ∷
   rw⁻ 138 (q18 c4) ∷
   rw⁻ 137 (q18 c4) ∷
   rw⁻ 136 (q16 c4) ∷
   rw⁻ 135 (q17 c4) ∷
   rw⁻ 134 (q17 c4) ∷
   rw⁻ 133 (q17 c4) ∷
   rw⁻ 132 (q15 c4) ∷
   rw⁻ 131 (q16 c4) ∷
   rw⁻ 130 (q18 c4) ∷
   rw⁻ 129 (q18 c4) ∷
   rw⁻ 128 (q16 c4) ∷
   rw⁻ 127 (q17 c4) ∷
   rw⁻ 126 (q19 c4) ∷
   rw⁻ 173 (q13 c4) ∷
   rw⁻ 172 (q20 c4) ∷
   rw⁻ 174 (q10 c4) ∷
   rw 173 (q21 c4) ∷
   rw⁻ 175 (q2 c4) ∷
   re 174 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 176 (q2 c4) ∷
   rw⁻ 176 (q5 c4) ∷
   rw 175 (q22 c4) ∷
   rw⁻ 177 (q2 c4) ∷
   rw⁻ 176 (q2 c4) ∷
   re 177 3 (CS13 ∷ []) ∷
   rw⁻ 178 (q10 c4) ∷
   rw 177 (q23 c4) ∷
   rw⁻ 179 (q13 c4) ∷
   rw⁻ 178 (q20 c4) ∷
   rw⁻ 179 (q24 c4) ∷
   rw 178 (q25 c4) ∷
   rw 179 (q26 c4) ∷
   rw 180 (q25 c4) ∷
   rw 181 (q26 c4) ∷
   rw 182 (q13 c4) ∷
   rw 177 (q27 c4) ∷
   rw 178 (q28 c4) ∷
   rw 179 (q27 c4) ∷
   rw 180 (q28 c4) ∷
   rw 181 (q10 c4) ∷
   rw 176 (q29 c4) ∷
   rw 177 (q1 c4) ∷
   rw 178 (q29 c4) ∷
   rw 179 (q1 c4) ∷
   rw 180 (q2 c4) ∷
   rw 175 (q3 c4) ∷
   rw 176 (q4 c4) ∷
   rw 177 (q3 c4) ∷
   rw 178 (q4 c4) ∷
   rw 179 (q5 c4) ∷
   rw 174 (q6 c4) ∷
   rw 175 (q7 c4) ∷
   rw 176 (q6 c4) ∷
   rw 177 (q7 c4) ∷
   rw 178 (q2 c4) ∷
   rw 173 (q8 c4) ∷
   rw 174 (q9 c4) ∷
   rw 175 (q8 c4) ∷
   rw 176 (q9 c4) ∷
   rw 177 (q10 c4) ∷
   rw 172 (q11 c4) ∷
   rw 173 (q12 c4) ∷
   rw 174 (q11 c4) ∷
   rw 175 (q12 c4) ∷
   rw 176 (q13 c4) ∷
   rw⁻ 171 (q17 c4) ∷
   rw⁻ 170 (q14 c4) ∷
   rw⁻ 169 (q15 c4) ∷
   rw⁻ 168 (q16 c4) ∷
   rw⁻ 167 (q17 c4) ∷
   rw⁻ 166 (q17 c4) ∷
   rw⁻ 165 (q16 c4) ∷
   rw⁻ 164 (q15 c4) ∷
   rw⁻ 163 (q14 c4) ∷
   rw⁻ 162 (q17 c4) ∷
   rw⁻ 161 (q17 c4) ∷
   rw⁻ 160 (q14 c4) ∷
   rw⁻ 159 (q18 c4) ∷ []) Eq.refl
